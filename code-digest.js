#!/usr/bin/env node

/**
 * codedigest.mjs - A Node.js script to generate a digest of a directory's structure and file contents.
 */

import {
  readFileSync, writeFileSync, existsSync, mkdirSync,
  lstatSync, readdirSync, readlinkSync, openSync,
  readSync, closeSync
} from 'node:fs';

import {
  join, extname, dirname, relative, resolve, sep, normalize
} from 'node:path';

////////////////////////////////////////////////////////////////////////////////
// Constants
////////////////////////////////////////////////////////////////////////////////

const MAX_FILE_SIZE        = 10 * 1024 * 1024;  // 10 MB
const MAX_DIRECTORY_DEPTH  = 20;
const MAX_TOTAL_SIZE_BYTES = 500 * 1024 * 1024; // 500 MB
const CHUNK_SIZE           = 1024 * 1024;       // 1 MB

/**
 * Default gitignore-style patterns to exclude.
 */
const DEFAULT_IGNORE_PATTERNS = new Set([
  '*.pyc',           '*.pyo',           '*.pyd',           '__pycache__',     '.pytest_cache',
  '.coverage',       '.tox',            '.nox',            '.mypy_cache',     '.ruff_cache',
  '.hypothesis',     'poetry.lock',     'Pipfile.lock',    'node_modules',    'bower_components',
  'package-lock.json','yarn.lock',      '.npm',            '.yarn',           '.pnpm-store',
  '*.class',         '*.jar',           '*.war',           '*.ear',           '*.nar',
  '.gradle/',        'build/',          '.settings/',      '.classpath',      'gradle-app.setting',
  '*.gradle',        '.project',        '*.o',             '*.obj',           '*.dll',
  '*.dylib',         '*.exe',           '*.lib',           '*.out',           '*.a',
  '*.pdb',           '.build/',         '*.xcodeproj/',    '*.xcworkspace/',  '*.pbxuser',
  '*.mode1v3',       '*.mode2v3',       '*.perspectivev3', '*.xcuserstate',   'xcuserdata/',
  '.swiftpm/',       '*.gem',           '.bundle/',        'vendor/bundle',   'Gemfile.lock',
  '.ruby-version',   '.ruby-gemset',    '.rvmrc',          'Cargo.lock',      '**/*.rs.bk',
  'target/',         'pkg/',            'obj/',            '*.suo',           '*.user',
  '*.userosscache',  '*.sln.docstates', 'packages/',       '*.nupkg',         'bin/',
  '.git',            '.svn',            '.hg',             '.gitignore',      '.gitattributes',
  '.gitmodules',     '*.svg',           '*.png',           '*.jpg',           '*.jpeg',
  '*.gif',           '*.ico',           '*.pdf',           '*.mov',           '*.mp4',
  '*.mp3',           '*.wav',           'venv',            '.venv',           'env',
  '.env',            'virtualenv',      '.idea',           '.vscode',         '.vs',
  '*.swo',           '*.swn',           '.settings',       '*.sublime-*',     '*.log',
  '*.bak',           '*.swp',           '*.tmp',           '*.temp',          '.cache',
  '.sass-cache',     '.eslintcache',    '.DS_Store',       'Thumbs.db',       'desktop.ini',
  'build',           'dist',            'target',          'out',             '*.egg-info',
  '*.egg',           '*.whl',           '*.so',            'site-packages',   '.docusaurus',
  '.next',           '.nuxt',           '*.min.js',        '*.min.css',       '*.map',
  '.terraform',      '*.tfstate*',      'vendor/',
]);

/**
 * ANSI escape codes for formatting console output.
 */
const FORMAT = {
  bold:   (text) => `\x1b[1m${text}\x1b[0m`,
  red:    (text) => `\x1b[31m${text}\x1b[0m`,
  green:  (text) => `\x1b[32m${text}\x1b[0m`,
  yellow: (text) => `\x1b[33m${text}\x1b[0m`,
  white:  (text) => `\x1b[37m${text}\x1b[0m`,
  gray:   (text) => `\x1b[90m${text}\x1b[0m`,
  invert: (text) => `\x1b[7m${text}\x1b[27m`,
};

////////////////////////////////////////////////////////////////////////////////
// Types
////////////////////////////////////////////////////////////////////////////////

/**
 * @typedef {Object} FileInfo
 * @property {string} path - The relative path of the file.
 * @property {string} content - The content of the file.
 * @property {number} size - The size of the file in bytes.
 */

/**
 * @typedef {Object} GitIgnoreRule
 * @property {string[]} segments
 * @property {boolean} negated
 * @property {boolean} directoryOnly
 * @property {boolean} anchored
 */

/**
 * @typedef {Object} ProcessingStats
 * @property {number} totalSize
 * @property {number} fileCount
 * @property {Set<string>} seenPaths
 * @property {Set<string>} seenSymlinks
 * @property {Array<{timestamp: string, message: string, stack?: string}>} errors
 * @property {number} skippedFiles
 * @property {number} filteredFiles
 * @property {number} nonTextFiles
 * @property {boolean} sizeLimitReached
 * @property {number} startTime
 * @property {Set<string>} matchedIgnorePatterns
 * @property {Set<string>} matchedIncludePatterns
 * @property {Object<string, number>} extensionSizes
 * @property {(e: Error) => void} addError
 */

/**
 * @typedef {Object} ProcessingOptions
 * @property {GitIgnoreRule[]} ignoreRules
 * @property {GitIgnoreRule[]} includeRules
 * @property {number} maxFileSize
 * @property {number} maxTotalSize
 * @property {number} maxDepth
 * @property {string} rootPath
 * @property {boolean} quiet
 * @property {boolean} ultraQuiet
 * @property {number} [currentDepth]
 */

////////////////////////////////////////////////////////////////////////////////
// Parsing Gitignore-Style Patterns
////////////////////////////////////////////////////////////////////////////////

function splitIntoSegments(pattern) {
  let segments = [];
  let current  = '';
  let escaped  = false;

  for (let i = 0; i < pattern.length; i++) {
    const ch = pattern[i];

    if (!escaped && ch === '\\') {
      escaped = true;
      continue;
    }

    if (!escaped && ch === '/') {
      if (current.length > 0) {
        segments.push(current);
      }
      current = '';
      continue;
    }

    current += ch;
    escaped = false;
  }

  if (current.length > 0) {
    segments.push(current);
  }

  return segments;
}

function parseGitignore(text) {
  const lines = text.split(/\r?\n/);
  const rules = [];

  outerLoop:
  for (let rawLine of lines) {
    let line = rawLine.trim();
    if (!line || line.startsWith('#')) {
      continue outerLoop; // skip blank or comment lines
    }

    let negated = false;
    if (line.startsWith('!')) {
      negated = true;
      line = line.slice(1);
    }

    let anchored = false;
    if (line.startsWith('/')) {
      anchored = true;
      line = line.slice(1);
    }

    let directoryOnly = false;
    if (line.endsWith('/')) {
      directoryOnly = true;
      line = line.slice(0, -1);
    }

    const segments = splitIntoSegments(line);

    rules.push({
      segments,
      negated,
      directoryOnly,
      anchored,
    });
  }

  return rules;
}

////////////////////////////////////////////////////////////////////////////////
// Matching Logic
////////////////////////////////////////////////////////////////////////////////

/**
 * "Last match wins": Return true if final match => non-negated, otherwise false.
 */
function matchPathByRules(filePath, rules, stats, matchedSetName) {
  const pathSegments = filePath.split('/').filter(Boolean);
  let matched = false;
  let matchedRule = null;

  for (const rule of rules) {
    if (matchesRule(pathSegments, rule)) {
      matched = !rule.negated;
      matchedRule = rule;
    }
  }

  if (matched && matchedRule && stats && matchedSetName) {
    const original = reconstructPattern(matchedRule);
    stats[matchedSetName].add(original);
  }
  return matched;
}

function matchesRule(pathSegments, rule) {
  if (rule.anchored) {
    return matchSegments(pathSegments, 0, rule.segments, 0, rule.directoryOnly);
  }
  for (let start = 0; start <= pathSegments.length; start++) {
    if (matchSegments(pathSegments, start, rule.segments, 0, rule.directoryOnly)) {
      return true;
    }
  }
  return false;
}

function matchSegments(pathSegs, pIndex, patSegs, sIndex, directoryOnly) {
  if (sIndex === patSegs.length) {
    if (directoryOnly) {
      return pIndex < pathSegs.length;
    }
    return true;
  }

  if (pIndex === pathSegs.length) {
    // only match if remaining pattern is all '**'
    for (let i = sIndex; i < patSegs.length; i++) {
      if (patSegs[i] !== '**') {
        return false;
      }
    }
    return true;
  }

  const token = patSegs[sIndex];
  if (token === '**') {
    // zero or more
    if (matchSegments(pathSegs, pIndex, patSegs, sIndex + 1, directoryOnly)) {
      return true;
    }
    for (let skip = pIndex; skip < pathSegs.length; skip++) {
      if (matchSegments(pathSegs, skip + 1, patSegs, sIndex, directoryOnly)) {
        return true;
      }
    }
    return false;
  }

  // single-segment match
  if (!segmentMatch(pathSegs[pIndex], token)) {
    return false;
  }

  return matchSegments(pathSegs, pIndex + 1, patSegs, sIndex + 1, directoryOnly);
}

function segmentMatch(pathSegment, patternSegment) {
  let regexStr = '';
  for (let i = 0; i < patternSegment.length; i++) {
    const ch = patternSegment[i];
    if (ch === '*') {
      regexStr += '[^/]*';
    } else if (ch === '?') {
      regexStr += '[^/]';
    } else {
      regexStr += escapeRegex(ch);
    }
  }
  const re = new RegExp(`^${regexStr}$`);
  return re.test(pathSegment);
}

function escapeRegex(ch) {
  return ch.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
}

function reconstructPattern(rule) {
  let p = rule.segments.map(s => s.replace(/\\/g, '\\\\').replace(/\//g, '\\/')).join('/');
  if (rule.directoryOnly) p += '/';
  if (rule.anchored) p = '/' + p;
  if (rule.negated) p = '!' + p;
  return p;
}

////////////////////////////////////////////////////////////////////////////////
// Include & Ignore Checking
////////////////////////////////////////////////////////////////////////////////

/**
 * Return true if the path matches the ignoreRules (i.e. "excluded").
 */
function isPathExcluded(filePath, ignoreRules, stats) {
  return matchPathByRules(filePath, ignoreRules, stats, 'matchedIgnorePatterns');
}

/**
 * Return true if the path matches the includeRules (i.e. "included").
 * If no includeRules, everything is included by default.
 */
function isPathIncluded(filePath, includeRules, stats) {
  if (!includeRules || includeRules.length === 0) {
    return true;
  }
  return matchPathByRules(filePath, includeRules, stats, 'matchedIncludePatterns');
}

////////////////////////////////////////////////////////////////////////////////
// Stats
////////////////////////////////////////////////////////////////////////////////

function createStats() {
  return {
    totalSize:             0,
    fileCount:             0,
    seenPaths:             new Set(),
    seenSymlinks:          new Set(),
    errors:                [],
    skippedFiles:          0,
    filteredFiles:         0,
    nonTextFiles:          0,
    sizeLimitReached:      false,
    startTime:             Date.now(),
    matchedIgnorePatterns: new Set(),
    matchedIncludePatterns: new Set(),
    extensionSizes:        {},

    addError(error) {
      this.errors.push({
        timestamp: new Date().toISOString(),
        message:   error.message,
        stack:     error.stack,
      });
    },
  };
}

////////////////////////////////////////////////////////////////////////////////
// File & Symlink Handling
////////////////////////////////////////////////////////////////////////////////

function readFileContent(filePath, maxFileSize) {
  try {
    const stats = lstatSync(filePath);

    if (stats.size > maxFileSize) {
      return `[File too large to display, size: ${formatBytes(stats.size)}]`;
    }

    if (!isTextFile(filePath)) {
      return '[Non-text file]';
    }

    if (stats.size > CHUNK_SIZE) {
      const fd     = openSync(filePath, 'r');
      const buffer = Buffer.alloc(CHUNK_SIZE);
      let content  = '';
      let bytesRead;

      try {
        while ((bytesRead = readSync(fd, buffer, 0, buffer.length, null)) !== 0) {
          content += buffer.toString('utf8', 0, bytesRead);
        }
      } finally {
        closeSync(fd);
      }
      return content;
    }

    return readFileSync(filePath, 'utf-8');
  } catch (error) {
    return `Error reading file: ${error.message}`;
  }
}

function isTextFile(filePath) {
  const textExtensions = new Set([
    '.txt',  '.md',   '.py',  '.js',   '.java', '.c',   '.cpp',  '.h',   '.hpp',
    '.cs',   '.go',   '.rs',  '.swift', '.rb',   '.php', '.html', '.css',
    '.json', '.xml',  '.yaml','.yml',   '.sh',   '.bat', '.sql',  '.csv',
    '.tsv',  '.ini',  '.cfg', '.toml',  '.lua',  '.pl',  '.pm',   '.r',
    '.ts'
  ]);

  if (textExtensions.has(extname(filePath).toLowerCase())) {
    return true;
  }

  try {
    const buffer = readFileSync(filePath, { encoding: 'utf8', flag: 'r' });
    return !buffer.includes('\0');
  } catch (error) {
    console.error(`Error checking if file is text: ${error.message}`);
    return false;
  }
}

function formatBytes(bytes, decimals = 2) {
  if (bytes === 0) return '0 Bytes';
  const k     = 1024;
  const dm    = decimals < 0 ? 0 : decimals;
  const sizes = ['Bytes', 'KB', 'MB', 'GB', 'TB', 'PB', 'EB', 'ZB', 'YB'];
  const i     = Math.floor(Math.log(bytes) / Math.log(k));
  return `${parseFloat((bytes / Math.pow(k, i)).toFixed(dm))} ${sizes[i]}`;
}

function processFile(filePath, maxFileSize, stats, files, rootPath, options) {
  try {
    const fileSize = lstatSync(filePath).size;

    if (fileSize > maxFileSize) {
      stats.skippedFiles++;
      if (!options.quiet && !options.ultraQuiet) {
        console.warn(`${FORMAT.bold('Skipping file larger than maxFileSize:')} ${filePath}`);
      }
      return;
    }

    if (stats.totalSize + fileSize > options.maxTotalSize) {
      stats.sizeLimitReached = true;
      if (!options.quiet && !options.ultraQuiet) {
        console.warn(`${FORMAT.bold('Total size limit reached at:')} ${filePath}`);
      }
      return;
    }

    if (!isTextFile(filePath)) {
      stats.nonTextFiles++;
      if (!options.quiet && !options.ultraQuiet) {
        console.warn(`${FORMAT.bold('Skipping non-text file:')} ${filePath}`);
      }
      return;
    }

    stats.totalSize += fileSize;
    stats.fileCount++;

    const ext = extname(filePath).toLowerCase().slice(1);
    stats.extensionSizes[ext] = (stats.extensionSizes[ext] || 0) + fileSize;

    const relativePath = relative(rootPath, filePath);
    files.push({
      path:    relativePath,
      content: readFileContent(filePath, maxFileSize),
      size:    fileSize,
    });

    if (!options.quiet && !options.ultraQuiet) {
      console.log(`${FORMAT.bold('Added to digest:')} ${relativePath}`);
    }
  } catch (error) {
    stats.addError(error);
    console.error(`Error processing file ${filePath}: ${error.message}`);
  }
}

function processSymlink(entryPath, targetPath, stats, files, options) {
  const symlinkKey = `${entryPath}:${targetPath}`;
  if (stats.seenSymlinks.has(symlinkKey)) {
    if (!options.ultraQuiet) {
      console.warn(`Circular symlink detected: ${entryPath} -> ${targetPath}`);
    }
    return [];
  }
  stats.seenSymlinks.add(symlinkKey);

  try {
    const targetStat = lstatSync(targetPath);
    if (targetStat.isDirectory()) {
      return processDirectory(targetPath, options, stats);
    } else {
      processFile(targetPath, options.maxFileSize, stats, files, options.rootPath, options);
      return [];
    }
  } catch (err) {
    if (!options.ultraQuiet) {
      console.warn(`Broken symlink or permission error: ${entryPath} -> ${targetPath}`);
    }
    return [];
  }
}

////////////////////////////////////////////////////////////////////////////////
// Directory Processing (Always Recurse, Only Apply Includes to Files)
////////////////////////////////////////////////////////////////////////////////

function processDirectory(
  dirPath,
  {
    ignoreRules,
    includeRules,
    maxFileSize     = MAX_FILE_SIZE,
    maxTotalSize    = MAX_TOTAL_SIZE_BYTES,
    maxDepth        = MAX_DIRECTORY_DEPTH,
    currentDepth    = 0,
    rootPath        = dirPath,
    quiet,
    ultraQuiet,
  },
  stats = createStats()
) {
  /** @type {FileInfo[]} */
  const files = [];

  if (currentDepth > maxDepth) {
    if (!ultraQuiet) {
      console.warn(`Max directory depth reached at ${dirPath}`);
    }
    return files;
  }

  const resolvedPath = resolve(dirPath);
  if (stats.seenPaths.has(resolvedPath)) {
    if (!ultraQuiet) {
      console.warn(`Circular reference detected at ${dirPath}, skipping.`);
    }
    return files;
  }
  stats.seenPaths.add(resolvedPath);

  let entries = [];
  try {
    entries = readdirSync(dirPath, { withFileTypes: true });
  } catch (error) {
    stats.addError(error);
    if (!ultraQuiet) {
      console.error(`Error reading directory ${dirPath}: ${error.message}`);
    }
    return files;
  }

  for (const entry of entries) {
    if (stats.sizeLimitReached) {
      break;
    }

    const entryPath = join(dirPath, entry.name);
    const relativePath = relative(rootPath, entryPath);
    const forwardSlashed = normalize(relativePath).split(sep).join('/');

    // First, check if ignored
    if (isPathExcluded(forwardSlashed, ignoreRules, stats)) {
      stats.filteredFiles++;
      continue;
    }

    // If it's a symlink, handle symlink logic
    if (entry.isSymbolicLink()) {
      try {
        const targetPath = resolve(dirname(entryPath), readlinkSync(entryPath));
        const symlinked = processSymlink(entryPath, targetPath, stats, files, {
          ignoreRules,
          includeRules,
          maxFileSize,
          maxTotalSize,
          maxDepth,
          currentDepth: currentDepth + 1,
          rootPath,
          quiet,
          ultraQuiet,
        });
        files.push(...symlinked);
      } catch (error) {
        stats.addError(error);
        if (!ultraQuiet) {
          console.error(`Error processing symlink ${entryPath}: ${error.message}`);
        }
      }
      continue;
    }

    // If it's a directory, always recurse unless it's ignored
    if (entry.isDirectory()) {
      const subFiles = processDirectory(
        entryPath,
        {
          ignoreRules,
          includeRules,
          maxFileSize,
          maxTotalSize,
          maxDepth,
          currentDepth: currentDepth + 1,
          rootPath,
          quiet,
          ultraQuiet,
        },
        stats
      );
      files.push(...subFiles);
      continue;
    }

    // If it's a file, now check if included
    if (!isPathIncluded(forwardSlashed, includeRules, stats)) {
      stats.filteredFiles++;
      continue;
    }

    // If we get here, it's a file that is not ignored and is included => process it
    processFile(entryPath, maxFileSize, stats, files, rootPath, {
      quiet,
      ultraQuiet,
    });
  }

  return files;
}

////////////////////////////////////////////////////////////////////////////////
// Directory Tree
////////////////////////////////////////////////////////////////////////////////

function generateDirectoryTree(
  dirPath,
  ignoreRules,
  includeRules,
  maxDepth,
  currentDepth = 0,
  prefix = '',
  rootPath = dirPath,
  result = { content: '', truncated: false },
  ultraQuiet = false
) {
  if (currentDepth > maxDepth || result.truncated) {
    return result.content;
  }

  let entries = [];
  try {
    entries = readdirSync(dirPath, { withFileTypes: true });
  } catch (error) {
    if (!ultraQuiet) {
      console.error(`Error generating directory tree for ${dirPath}: ${error.message}`);
    }
    return result.content;
  }

  // We use a similar approach:
  // - Skip if path is excluded, but always show directories (unless excluded).
  // - Only show file if it's included.
  const filtered = entries.filter((entry) => {
    const relPath = relative(rootPath, join(dirPath, entry.name));
    const fwd = normalize(relPath).split(sep).join('/');

    // If ignored, skip
    if (isPathExcluded(fwd, ignoreRules, null)) {
      return false;
    }

    // If directory, we keep it in the tree for traversal
    if (entry.isDirectory() || entry.isSymbolicLink()) {
      return true;
    }

    // If a file, we also check isPathIncluded
    return isPathIncluded(fwd, includeRules, null);
  });

  filtered.forEach((entry, index) => {
    if (result.content.length > CHUNK_SIZE) {
      result.truncated = true;
      return;
    }

    const isLast = index === filtered.length - 1;
    const entryPath = join(dirPath, entry.name);
    const line = `${prefix}${isLast ? '└── ' : '├── '}${entry.name}${entry.isDirectory() ? '/' : ''}\n`;
    result.content += line;

    if (entry.isDirectory() && !result.truncated) {
      generateDirectoryTree(
        entryPath,
        ignoreRules,
        includeRules,
        maxDepth,
        currentDepth + 1,
        `${prefix}${isLast ? '    ' : '│   '}`,
        rootPath,
        result,
        ultraQuiet
      );
    }
  });

  return result.truncated
    ? result.content + '\n[Directory tree truncated due to size]'
    : result.content;
}

////////////////////////////////////////////////////////////////////////////////
// Summary & Reporting
////////////////////////////////////////////////////////////////////////////////

function calculateExtensionPercentages(extensionSizes, totalSize) {
  const percentages = {};
  for (const ext in extensionSizes) {
    percentages[ext] = totalSize > 0
      ? (extensionSizes[ext] / totalSize) * 100
      : 0;
  }
  return percentages;
}

function generateBarGraph(extensionPercentages) {
  const { white, green } = FORMAT;
  const barLength = 20;
  let graph = '';

  const sorted = Object.entries(extensionPercentages)
    .sort(([, a], [, b]) => b - a);

  for (const [ext, percent] of sorted) {
    const filledBars = Math.round((percent / 100) * barLength);
    const emptyBars  = barLength - filledBars;
    const bar        = '█'.repeat(filledBars) + '–'.repeat(emptyBars);
    graph += `${white(ext.padEnd(12))}: ${green(bar)} ${percent.toFixed(1)}%\n`;
  }
  return graph;
}

function generateSummary(path, stats, options, outputFile) {
  const { bold, red, green, yellow, white, gray, invert } = FORMAT;
  const executionTime = Date.now() - stats.startTime;

  const extensionPercentages = calculateExtensionPercentages(
    stats.extensionSizes,
    stats.totalSize
  );
  const barGraph = generateBarGraph(extensionPercentages);

  return `
${invert(bold(' Digest Summary '))}
${white('Processed directory:')}         ${gray(resolve(path))}
${white('Execution time:')}              ${yellow((executionTime / 1000).toFixed(2))} ${gray('seconds')}
${white('Files added to digest:')}       ${green(stats.fileCount.toString())}
${white('Files excluded by pattern:')}   ${red(stats.filteredFiles.toString())}
${white('Files excluded (non-text):')}   ${red(stats.nonTextFiles.toString())}
${white('Files skipped (size limit):')}  ${red(stats.skippedFiles.toString())}
${white('Total size:')}                  ${yellow(formatBytes(stats.totalSize))}
${white('Size limit reached:')}          ${stats.sizeLimitReached ? red('Yes') : green('No')}

${invert(bold(' Configuration '))}
${white('Max file size:')}       ${yellow(formatBytes(options.maxFileSize))}
${white('Max total size:')}      ${yellow(formatBytes(options.maxTotalSize))}
${white('Max directory depth:')} ${yellow(options.maxDepth)}

${bold('Ignore patterns that matched:')} ${
    stats.matchedIgnorePatterns.size > 0
      ? `\n  ${gray(Array.from(stats.matchedIgnorePatterns).join('\n  '))}`
      : 'None'
}

${bold('Include patterns that matched:')} ${
    stats.matchedIncludePatterns.size > 0
      ? `\n  ${gray(Array.from(stats.matchedIncludePatterns).join('\n  '))}`
      : 'None'
}

${invert(bold(' File Size by Extension '))}
${barGraph}

${invert(bold(` Errors (${stats.errors.length}) `))}
${
    stats.errors.length
      ? stats.errors.map((err) => `${err.timestamp}: ${err.message}`).join('\n')
      : 'No errors occurred'
}

${invert(bold(' Digest File '))}
${outputFile}
`;
}

////////////////////////////////////////////////////////////////////////////////
// CLI & Main
////////////////////////////////////////////////////////////////////////////////

function printHelp() {
  console.log(`
Usage: node codedigest.mjs [options]

Options:
  --path <path>, -p <path>                   Directory to process (default: current directory)
  --output <file>, -o <file>                 Output file path (default: digest.txt)
  --ignore <file>, -g <file>                 File containing ignore patterns (gitignore-style)
  --include <file>, -n <file>                File containing include patterns (gitignore-style)
  --ignore-pattern <pattern>, -i <pattern>   Additional ignore pattern (can be used multiple times)
  --include-pattern <pattern>, -I <pattern>  Additional include pattern (can be used multiple times)
  --max-size <bytes>, -s <bytes>             Maximum file size (default: ${formatBytes(MAX_FILE_SIZE)})
  --max-total-size <bytes>, -t <bytes>       Maximum total size (default: ${formatBytes(MAX_TOTAL_SIZE_BYTES)})
  --max-depth <number>, -d <number>          Maximum directory depth (default: ${MAX_DIRECTORY_DEPTH})
  --quiet, -q                                Suppress 'Added' and 'Skipped' messages
  --ultra-quiet, -uq                         Suppress all non-error output
  --skip-default-ignore, -k                  Skip default ignore patterns; use only user-provided
  --help, -h                                 Display this help message
`);
}

function validateArgs(args) {
  const errors = [];
  if (args.maxSize <= 0) {
    errors.push('maxSize must be positive');
  }
  if (args.maxTotalSize <= 0) {
    errors.push('maxTotalSize must be positive');
  }
  if (args.maxDepth <= 0) {
    errors.push('maxDepth must be positive');
  }
  if (args.ignoreFile && !existsSync(args.ignoreFile)) {
    errors.push(`Ignore file not found: ${args.ignoreFile}`);
  }
  if (args.includeFile && !existsSync(args.includeFile)) {
    errors.push(`Include file not found: ${args.includeFile}`);
  }
  if (errors.length > 0) {
    throw new Error(`Invalid arguments:\n${errors.join('\n')}`);
  }
}

function parseArgs() {
  const argv = process.argv.slice(2);
  const parsed = {
    path: '.', outputFile: 'digest.txt',
    ignoreFile: null, includeFile: null,
    ignorePatterns: [], includePatterns: [],
    maxSize: MAX_FILE_SIZE, maxTotalSize: MAX_TOTAL_SIZE_BYTES,
    maxDepth: MAX_DIRECTORY_DEPTH,
    quiet: false, ultraQuiet: false,
    skipDefaultIgnore: false,
  };

  for (let i = 0; i < argv.length; i++) {
    const arg = argv[i];
    switch (arg) {
      case '--path': case '-p':
        parsed.path = argv[++i]; break;
      case '--output': case '-o':
        parsed.outputFile = argv[++i]; break;
      case '--ignore': case '-g':
        parsed.ignoreFile = argv[++i]; break;
      case '--include': case '-n':
        parsed.includeFile = argv[++i]; break;
      case '--ignore-pattern': case '-i':
        parsed.ignorePatterns.push(argv[++i]); break;
      case '--include-pattern': case '-I':
        parsed.includePatterns.push(argv[++i]); break;
      case '--max-size': case '-s':
        parsed.maxSize = parseInt(argv[++i], 10); break;
      case '--max-total-size': case '-t':
        parsed.maxTotalSize = parseInt(argv[++i], 10); break;
      case '--max-depth': case '-d':
        parsed.maxDepth = parseInt(argv[++i], 10); break;
      case '--quiet': case '-q':
        parsed.quiet = true; break;
      case '--ultra-quiet': case '-uq':
        parsed.ultraQuiet = true; break;
      case '--skip-default-ignore': case '-k':
        parsed.skipDefaultIgnore = true; break;
      case '--help': case '-h':
        printHelp(); process.exit(0);
      default:
        console.warn(`Unknown option: ${arg}`);
        printHelp();
        process.exit(1);
    }
  }
  return parsed;
}

function loadPatternFile(filePath) {
  try {
    return readFileSync(filePath, 'utf-8');
  } catch (err) {
    console.error(`Error reading pattern file ${filePath}: ${err.message}`);
    return '';
  }
}

function ensureDirectoryExists(dirPath) {
  if (!existsSync(dirPath)) {
    mkdirSync(dirPath, { recursive: true });
  }
}

////////////////////////////////////////////////////////////////////////////////
// Main
////////////////////////////////////////////////////////////////////////////////

async function main() {
  try {
    const args = parseArgs();
    validateArgs(args);

    const rootPath       = resolve(args.path);
    const outputFilePath = resolve(args.outputFile);

    if (!existsSync(rootPath)) {
      throw new Error(`Path does not exist: ${args.path}`);
    }
    if (!lstatSync(rootPath).isDirectory()) {
      throw new Error(`Path is not a directory: ${args.path}`);
    }

    // 1) Build final ignoreRules
    let ignoreText = '';
    if (!args.skipDefaultIgnore) {
      ignoreText += Array.from(DEFAULT_IGNORE_PATTERNS).join('\n') + '\n';
    }
    if (args.ignoreFile) {
      ignoreText += loadPatternFile(args.ignoreFile) + '\n';
    }
    if (args.ignorePatterns.length > 0) {
      ignoreText += args.ignorePatterns.join('\n') + '\n';
    }
    const ignoreRules = parseGitignore(ignoreText);

    // 2) Build final includeRules
    let includeText = '';
    if (args.includeFile) {
      includeText += loadPatternFile(args.includeFile) + '\n';
    }
    if (args.includePatterns.length > 0) {
      includeText += args.includePatterns.join('\n') + '\n';
    }
    const includeRules = parseGitignore(includeText);

    // Exclude the output file itself if inside the root
    if (outputFilePath.startsWith(rootPath)) {
      const rel = relative(rootPath, outputFilePath).split(sep).join('/');
      ignoreRules.push({
        segments: splitIntoSegments(rel),
        negated: false,
        directoryOnly: false,
        anchored: false,
      });
    }

    const options = {
      ignoreRules,
      includeRules,
      maxFileSize:  args.maxSize,
      maxTotalSize: args.maxTotalSize,
      maxDepth:     args.maxDepth,
      rootPath,
      quiet:        args.quiet,
      ultraQuiet:   args.ultraQuiet,
    };

    const statsObj = createStats();
    const files    = processDirectory(args.path, options, statsObj);

    // Build file content digest
    const digestContent = files.map((file) => {
      const sepLine = '='.repeat(48) + '\n';
      return `${sepLine}File: ${file.path}\n${sepLine}${file.content}\n`;
    }).join('');

    // Build directory tree
    const directoryTree = generateDirectoryTree(
      args.path,
      ignoreRules,
      includeRules,
      args.maxDepth,
      0,
      '',
      rootPath,
      { content: '', truncated: false },
      args.ultraQuiet
    );

    const summary = generateSummary(args.path, statsObj, options, args.outputFile);

    ensureDirectoryExists(dirname(outputFilePath));
    writeFileSync(
      outputFilePath,
      `Directory Structure\n==================\n${directoryTree}\n\n` +
      `File Contents\n=============\n${digestContent}\n\n${summary}`
    );

    if (!args.ultraQuiet) {
      console.log(summary);
    }

    if (statsObj.errors.length > 0 && !args.ultraQuiet) {
      console.warn(
        `\nWarning: ${statsObj.errors.length} errors occurred during processing. Check console for details.`
      );
    }
  } catch (error) {
    console.error(`Fatal error: ${error.message}`);
    process.exit(1);
  }
}

main().catch((error) => {
  console.error('Unhandled error:', error);
  process.exit(1);
});