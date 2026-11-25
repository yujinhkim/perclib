import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import {execFileSync} from 'node:child_process';
import {wikiRoot, readArticles, readRegistry, validateTags, assertionsIn} from '../scripts/articles.mjs';
import {checkArticles, checkHistory} from '../scripts/check-articles.mjs';

const articles = await readArticles();
const ledger = await readRegistry();
const first = assertionsIn(articles)[0];
const clone = value => structuredClone(value);
const mutateFirst = (copy, change) => {
  const section = copy.find(a=>a.id===first.article).sections.find(s=>s.id===first.section);
  section.html = change(section.html);
};

test('migration preserves all twelve articles, contexts, section titles, prose, formulas and links', async () => {
  const result = await checkArticles();
  const original = result.articles.filter(a => Object.hasOwn(result.baseline.articles, a.id));
  assert.equal(original.length, 12);
  assert.equal(assertionsIn(original).length, 65);
});

test('duplicate assertion across articles is rejected', () => {
  const copy = clone(articles);
  copy.at(-1).sections[0].html += `<a id="tag-${first.tag}" data-assertion="definition" data-title="Duplicate"></a>`;
  assert.throws(()=>validateTags(copy,ledger),/Duplicate assertion/);
});

test('malformed and unallocated anchors cannot silently disappear from validation', () => {
  for (const replacement of ['abc!', 'abc', 'AAAAA']) {
    const copy = clone(articles);
    mutateFirst(copy, html=>html.replace(`tag-${first.tag}`,`tag-${replacement}`));
    assert.throws(()=>validateTags(copy,ledger),/malformed assertion/);
  }
  const empty = {version:1,tags:[]};
  assert.throws(()=>validateTags(articles,empty),/Unallocated/);
});

test('duplicate or malformed ledger reservations fail', () => {
  const copy=clone(ledger); copy.tags.push(copy.tags[0]);
  assert.throws(()=>validateTags([],copy),/Duplicate ledger/);
  for (const tag of ['abc!', 1234]) {
    copy.tags=[{tag,state:'allocated'}];
    assert.throws(()=>validateTags([],copy),/Malformed ledger/);
  }
});

test('withdrawn assertions cannot use tombstones', () => {
  const copy=clone(ledger); copy.tags.find(x=>x.tag===first.tag).state='withdrawn';
  assert.throws(()=>validateTags(articles,copy),/withdrawn/);
});

test('history rejects deleted reservations, resurrected tombstones and unrecorded withdrawals', () => {
  const previous=clone(ledger); previous.tags.push({tag:'ZZZZ',state:'withdrawn'});
  assert.throws(()=>validateTags(articles,ledger,previous),/Reserved tag removed/);
  const resurrected=clone(previous); resurrected.tags.at(-1).state='allocated';
  assert.throws(()=>validateTags(articles,resurrected,previous),/Tombstone resurrected/);
  const copy=clone(articles);
  mutateFirst(copy,html=>html.replace(new RegExp(`<a id="tag-${first.tag}"[^>]*></a>`),''));
  assert.throws(()=>validateTags(copy,ledger,ledger,[first]),/needs a tombstone/);
  const withdrawn=clone(ledger); withdrawn.tags.find(x=>x.tag===first.tag).state='withdrawn';
  assert.doesNotThrow(()=>validateTags(copy,withdrawn,ledger,[first]));
});

test('allocator reserves unique tags atomically and retains withdrawals', async () => {
  const root=await fs.mkdtemp(path.join(os.tmpdir(),'wiki-tags-'));
  try {
    await fs.cp(path.join(wikiRoot,'scripts'),path.join(root,'scripts'),{recursive:true});
    await fs.mkdir(path.join(root,'articles'));
    await fs.writeFile(path.join(root,'tags.json'),JSON.stringify({version:1,tags:[{tag:'0000',state:'withdrawn'}]}));
    const command=path.join(root,'scripts/new_tag');
    const tags=Array.from({length:8},()=>execFileSync(process.execPath,[command],{encoding:'utf8'}).trim());
    assert.equal(new Set(tags).size,8);
    for(const tag of tags){assert.match(tag,/^[0-9A-Z]{4}$/);assert.notEqual(tag,'0000');}
    execFileSync(process.execPath,[command,'--withdraw',tags[0]]);
    const updated=JSON.parse(await fs.readFile(path.join(root,'tags.json')));
    assert.equal(updated.tags.length,9);
    assert.equal(updated.tags.find(x=>x.tag===tags[0]).state,'withdrawn');
    await fs.writeFile(path.join(root,'.tags.lock'),'');
    assert.throws(()=>execFileSync(process.execPath,[command],{stdio:'pipe'}),/Command failed/);
    assert.deepEqual(JSON.parse(await fs.readFile(path.join(root,'tags.json'))),updated);
  } finally {await fs.rm(root,{recursive:true,force:true});}
});

test('history comparison works in a real checkout and rejects a removed reservation', async () => {
  const repo=await fs.mkdtemp(path.join(os.tmpdir(),'wiki-history-'));
  const root=path.join(repo,'wiki');
  const git=args=>execFileSync('git',args,{cwd:repo,stdio:'pipe'});
  try {
    await fs.mkdir(root);
    await fs.cp(path.join(wikiRoot,'articles'),path.join(root,'articles'),{recursive:true});
    await fs.writeFile(path.join(root,'tags.json'),JSON.stringify(ledger));
    git(['init']); git(['add','.']); git(['-c','user.name=Test','-c','user.email=test@example.invalid','commit','-m','baseline']);
    await checkHistory(root,'HEAD');
    const copy=clone(ledger);copy.tags.push({tag:'ZZZZ',state:'withdrawn'});
    await fs.writeFile(path.join(root,'tags.json'),JSON.stringify(copy));
    git(['add','.']);git(['-c','user.name=Test','-c','user.email=test@example.invalid','commit','-m','reserve']);
    await fs.writeFile(path.join(root,'tags.json'),JSON.stringify(ledger));
    await assert.rejects(checkHistory(root,'HEAD'),/Reserved tag removed/);
  } finally {await fs.rm(repo,{recursive:true,force:true});}
});

test('later articles do not weaken the original migration baseline', async () => {
  const temp=await fs.mkdtemp(path.join(os.tmpdir(),'wiki-extension-'));
  try {
    for(const name of ['articles','tags.json','migration-baseline.json'])await fs.cp(path.join(wikiRoot,name),path.join(temp,name),{recursive:true});
    const result=await checkArticles(temp);
    assert.ok(result.articles.some(a=>a.id==='harris-inequality'));
    const originalPath=path.join(temp,'articles/product-model.md'), original=await fs.readFile(originalPath,'utf8');
    await fs.writeFile(originalPath,original.replace('</p>','Changed.</p>'));
    await assert.rejects(checkArticles(temp),/exposition changed/);
    await fs.rm(originalPath);
    await assert.rejects(checkArticles(temp),/Migrated article missing/);
  }finally{await fs.rm(temp,{recursive:true,force:true});}
});
