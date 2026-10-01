// Bundles src/ into a single self-contained HTML file: dist/rat-proto.html
import { readFileSync, writeFileSync, mkdirSync } from 'node:fs';

const html = readFileSync('src/index.html', 'utf8');
const css = readFileSync('src/style.css', 'utf8');
const js = readFileSync('src/game.js', 'utf8');

const out = html
  .replace('<link rel="stylesheet" href="style.css">', () => `<style>\n${css}</style>`)
  .replace('<script src="game.js"></script>', () => `<script>\n${js}</script>`);

mkdirSync('dist', { recursive: true });
writeFileSync('dist/rat-proto.html', out);
console.log(`dist/rat-proto.html (${(out.length / 1024).toFixed(1)} KB)`);
