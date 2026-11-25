import fs from 'node:fs/promises';
import path from 'node:path';
import {createHash} from 'node:crypto';
import {execFileSync} from 'node:child_process';
import {wikiRoot, readArticles, readRegistry, validateTags, stripAnchors, anchorPattern} from './articles.mjs';

const hash = text => createHash('sha256').update(text).digest('hex');
export async function checkArticles(root = wikiRoot) {
  const articles = await readArticles(root);
  const ledger = await readRegistry(root);
  const assertions = validateTags(articles, ledger);
  const baseline = JSON.parse(await fs.readFile(path.join(root, 'migration-baseline.json'), 'utf8'));
  for (const id of Object.keys(baseline.articles)) {
    if (!articles.some(a => a.id === id)) throw Error(`Migrated article missing: ${id}`);
  }
  for (const article of articles) {
    const original = baseline.articles[article.id];
    if (new Set(article.sections.map(s => s.id)).size !== article.sections.length) throw Error(`${article.id}: duplicate section`);
    if (!assertions.some(a => a.article === article.id)) throw Error(`${article.id}: missing assertion tags`);
    if (!original) continue; // Later articles are validated, without rewriting the migration baseline.
    const {sections, ...metadata} = article;
    if (hash(JSON.stringify(metadata)) !== original.metadataSha256) throw Error(`${article.id}: metadata changed from migration baseline`);
    if (sections.length !== Object.keys(original.sections).length) throw Error(`${article.id}: section count changed`);
    const seen = new Set();
    for (const s of sections) {
      if (seen.has(s.id)) throw Error(`${article.id}: duplicate section ${s.id}`);
      seen.add(s.id);
      const expected = original.sections[s.id];
      if (!expected || expected.title !== s.title || hash(stripAnchors(s.html)) !== expected.sha256) throw Error(`${article.id}/${s.id}: exposition changed from migration baseline`);
    }
    if (!assertions.some(a => a.article === article.id)) throw Error(`${article.id}: missing assertion tags`);
  }
  return {articles, assertions, baseline};
}

// Local builds need neither a network connection nor Lean. In GitHub CI, compare
// against the event's base commit, fetching just that commit if checkout is shallow.
export async function checkHistory(root = wikiRoot, base) {
  const git = args => execFileSync('git', args, {cwd:path.resolve(root, '..'), encoding:'utf8', stdio:['ignore','pipe','pipe']}).trim();
  if (!base && process.env.GITHUB_ACTIONS === 'true') {
    const event = JSON.parse(await fs.readFile(process.env.GITHUB_EVENT_PATH, 'utf8'));
    base = event.pull_request?.base?.sha ?? event.before;
    if (!base || /^0+$/.test(base)) throw Error('CI cannot identify a tag-history base commit');
    if (!/^[a-f0-9]{40}$/.test(base)) throw Error('Invalid CI base SHA');
    try { git(['cat-file','-e',`${base}^{commit}`]); }
    catch { git(['fetch','--no-tags','--depth=1','origin',base]); }
  }
  if (!base) {
    try { git(['rev-parse','--show-toplevel']); base = 'HEAD'; }
    catch { return; } // Source archives are also buildable without a .git directory.
  }
  git(['cat-file','-e',`${base}^{commit}`]);
  if (!git(['ls-tree','--name-only',base,'--','wiki/tags.json'])) return;
  const previous = JSON.parse(git(['show',`${base}:wiki/tags.json`]));
  const names = git(['ls-tree','-r','--name-only',base,'--','wiki/articles']).split('\n').filter(n=>n.endsWith('.md'));
  const previousAssertions = names.flatMap(name => [...git(['show',`${base}:${name}`]).matchAll(anchorPattern)].map(m=>({tag:m[1]})));
  validateTags(await readArticles(root), await readRegistry(root), previous, previousAssertions);
}

if (process.argv[1] === new URL(import.meta.url).pathname) {
  const {articles, assertions} = await checkArticles();
  await checkHistory(wikiRoot, process.argv[2]);
  console.log(`Validated ${articles.length} unchanged articles and ${assertions.length} unique assertion tags.`);
}
