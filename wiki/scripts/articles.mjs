import fs from 'node:fs/promises';
import path from 'node:path';
import {fileURLToPath} from 'node:url';

export const wikiRoot = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
export const tagPattern = /^[0-9A-Z]{4}$/;
// Invisible citation anchors leave the original exposition and layout intact.
export const anchorPattern = /<a id="tag-([0-9A-Z]{4})" data-assertion="(definition|proposition|theorem|corollary)" data-title="([^"<>]+)"><\/a>/g;
export const stripAnchors = text => text.replace(anchorPattern, '');

export async function readArticles(root = wikiRoot) {
  const names = (await fs.readdir(path.join(root, 'articles'))).filter(n => n.endsWith('.md')).sort();
  return Promise.all(names.map(async name => {
    const text = await fs.readFile(path.join(root, 'articles', name), 'utf8');
    const front = /^---\n([\s\S]*?)\n---\n\n/.exec(text);
    if (!front) throw Error(`${name}: missing JSON front matter (a YAML subset)`);
    const metadata = JSON.parse(front[1]);
    if (metadata.id !== name.slice(0, -3)) throw Error(`${name}: article ID must match filename`);
    if ('tag' in metadata || 'status' in metadata || 'sections' in metadata) throw Error(`${name}: assertion tags/statuses are not article metadata`);
    const body = text.slice(front[0].length);
    const headings = [...body.matchAll(/^## (.+) \{#section-([a-z0-9-]+)\}\n\n/gm)];
    if (!headings.length || headings[0].index !== 0) throw Error(`${name}: expected section headings`);
    const sections = headings.map((h, i) => {
      const raw = body.slice(h.index + h[0].length, headings[i+1]?.index ?? body.length);
      const suffix = i === headings.length - 1 ? '\n' : '\n\n';
      if (!raw.endsWith(suffix)) throw Error(`${name}/${h[2]}: missing section separator`);
      return {id:h[2], title:h[1], html:raw.slice(0, -suffix.length)};
    });
    return {...metadata, sections};
  }));
}

export function assertionsIn(articles) {
  return articles.flatMap(article => article.sections.flatMap(section =>
    [...section.html.matchAll(anchorPattern)].map(m => ({tag:m[1], kind:m[2], title:m[3], article:article.id, section:section.id, anchor:`tag-${m[1]}`}))));
}

export async function readRegistry(root = wikiRoot) {
  return JSON.parse(await fs.readFile(path.join(root, 'tags.json'), 'utf8'));
}

export function validateTags(articles, registry, previous = null, previousAssertions = []) {
  if (registry.version !== 1 || !Array.isArray(registry.tags)) throw Error('Invalid tag ledger');
  const reserved = new Map();
  for (const entry of registry.tags) {
    if (typeof entry.tag !== 'string' || !tagPattern.test(entry.tag) || !['allocated','withdrawn'].includes(entry.state)) throw Error(`Malformed ledger entry: ${JSON.stringify(entry)}`);
    if (reserved.has(entry.tag)) throw Error(`Duplicate ledger tag: ${entry.tag}`);
    reserved.set(entry.tag, entry.state);
  }
  const assertions = assertionsIn(articles);
  const used = new Set();
  for (const a of assertions) {
    if (used.has(a.tag)) throw Error(`Duplicate assertion tag: ${a.tag}`);
    if (reserved.get(a.tag) !== 'allocated') throw Error(`Unallocated or withdrawn assertion tag: ${a.tag}`);
    used.add(a.tag);
  }
  for (const article of articles) {
    for (const section of article.sections) {
      const stripped = stripAnchors(section.html);
      if (/data-assertion|id\s*=\s*["']tag-/.test(stripped)) throw Error(`${article.id}/${section.id}: malformed assertion anchor`);
      if (/\b(?:Lrp|PercLib|Mathlib)\.[A-Za-z_]/.test(stripped)) throw Error(`${article.id}: Lean declaration name in article content`);
    }
  }
  if (previous) {
    for (const entry of previous.tags) {
      if (!reserved.has(entry.tag)) throw Error(`Reserved tag removed: ${entry.tag}`);
      if (entry.state === 'withdrawn' && reserved.get(entry.tag) !== 'withdrawn') throw Error(`Tombstone resurrected: ${entry.tag}`);
    }
    for (const {tag} of previousAssertions) {
      if (!used.has(tag) && reserved.get(tag) !== 'withdrawn') throw Error(`Removed assertion needs a tombstone: ${tag}`);
    }
  }
  return assertions;
}
