import test from 'node:test';
import assert from 'node:assert/strict';
import {historyCsv, dailyHistoryCsv, fileHistoryCsv, historyCountFields} from '../src/history-csv.mjs';
import {historyPage} from '../src/history.mjs';

test('CSV preserves all counters and chronology, with no invented initial delta', () => {
  const counts = [5, 8, 3].map(n => Object.fromEntries(historyCountFields.map((key, i) => [key, n + i])));
  const history = {available:true, tip:'c'.repeat(40), shallow:true, selection:'Fixture', comparison:{available:true, reference:'fixture', referenceCommit:'d'.repeat(40), relationship:'diverged', snapshot:{...counts[0], date:'2026-11-14T00:00:00Z'}}, snapshots:counts.map((count, i) => ({...count, commit:String.fromCharCode(97+i).repeat(40), date:['2026-11-15T01:00:00+01:00','2026-11-14T23:30:00Z','2026-11-15T02:00:00Z'][i]}))};
  const [header, ...lines] = historyCsv(history).trimEnd().split('\r\n').map(line => line.split(','));
  const rows = lines.map(line => Object.fromEntries(header.map((key, i) => [key, line[i]])));
  for (let i = 0; i < rows.length; i++) {
    assert.equal(rows[i].selectedTip, history.tip);
    assert.equal(rows[i].referenceCommit, history.comparison.referenceCommit);
    assert.equal(rows[i].referenceRelationship, 'diverged');
    assert.equal(rows[i].commit, history.snapshots[i].commit);
    assert.equal(rows[i].date, history.snapshots[i].date);
    assert.equal(rows[i].shallow, 'true');
    assert.equal(rows[i].snapshotIndex, String(i));
    for (const key of historyCountFields) {
      assert.equal(Number(rows[i][key]), history.snapshots[i][key]);
      assert.equal(rows[i][key+'Delta'], i ? String(history.snapshots[i][key] - history.snapshots[i-1][key]) : '');
    }
  }
  for (const key of historyCountFields) assert.equal(rows.slice(1).reduce((total, row) => total + Number(row[key+'Delta']), 0), counts.at(-1)[key] - counts[0][key]);
  for (const kind of ['library','wiki']) {
    assert.match(historyPage(history,kind), /href="\/metrics\/history.csv" download=/);
    assert.match(historyPage(history,kind), /href="\/metrics\/history-daily.csv" download=/);
  }
  assert.equal(historyCsv({available:false,snapshots:[]}), null);
  assert.ok(historyCsv({...history, comparison:undefined}).split('\r\n')[1].startsWith(history.tip + ',true,,,0,'));
  assert.doesNotMatch(historyPage({available:false},'wiki'), /history.csv/);
});

test('older saved counters remain unavailable rather than zero in CSV', () => {
  const history = {available:true, tip:'old', shallow:false, snapshots:[
    {commit:'a', date:'2026-11-14', articles:1},
    {commit:'b', date:'2026-11-15', articles:2},
  ]};
  const [header, ...rows] = historyCsv(history).trimEnd().split('\r\n').map(line => line.split(','));
  for (const key of ['readingMaps', 'readingMapWords', 'readingMapsDelta', 'readingMapWordsDelta'])
    assert.ok(rows.every(row => row[header.indexOf(key)] === ''));
  assert.equal(rows[1][header.indexOf('articlesDelta')], '1');
});


test('daily CSV groups UTC transitions without sorting the commit chain', () => {
  const history = {available:true, tip:'d', shallow:true, snapshots:[
    {commit:'a', date:'2026-11-15T00:30:00+01:00', articles:4},
    {commit:'b', date:'2026-11-16T01:00:00Z', articles:9},
    {commit:'c', date:'2026-11-15T23:00:00Z', articles:6},
    {commit:'d', date:'2026-11-16T03:00:00Z', articles:8},
  ]};
  const [header, ...lines] = dailyHistoryCsv(history).trimEnd().split('\r\n').map(line => line.split(','));
  const rows = lines.map(line => Object.fromEntries(header.map((key, i) => [key, line[i]])));
  assert.deepEqual(rows.map(r => r.utcDate), ['2026-11-14','2026-11-15','2026-11-16']);
  assert.deepEqual(rows.map(r => r.articlesDelta), ['0','-3','7']);
  assert.deepEqual(rows.map(r => r.recordedSnapshots), ['1','1','2']);
  assert.deepEqual(rows.map(r => r.baselineObserved), ['true','false','false']);
  assert.ok(rows.every(r => r.readingMapsDelta === '' && r.selectedTip === 'd' && r.shallow === 'true'));
  assert.equal(rows.reduce((sum,r) => sum + Number(r.articlesDelta), 0), 4);
  assert.equal(dailyHistoryCsv({available:false}), null);
});

test('daily CSV leaves an entire partially observed daily counter unavailable', () => {
  const history = {available:true, tip:'c', shallow:false, snapshots:[
    {commit:'a', date:'2026-11-15T01:00:00Z'},
    {commit:'b', date:'2026-11-15T02:00:00Z', readingMaps:1},
    {commit:'c', date:'2026-11-15T03:00:00Z', readingMaps:3},
  ]};
  const [header,row] = dailyHistoryCsv(history).trimEnd().split('\r\n').map(line => line.split(','));
  assert.equal(row[header.indexOf('readingMapsDelta')], '');
});


const parseSimpleCsv = csv => {
  const [header, ...rows] = csv.trimEnd().split('\r\n').map(line => line.split(','));
  return rows.map(row => Object.fromEntries(header.map((key,i) => [key,row[i]])));
};
test('file CSV distinguishes additions, removals and changed blobs with equal counts', () => {
  const file = (path,blob,n) => ({path,blob,kind:'library',counts:{leanLines:n}});
  const history = {available:true, tip:'tip', shallow:false,
    files:[file('PercLib/new.lean','new',7), file('PercLib/same.lean','new-body',3)],
    comparison:{available:true, referenceCommit:'base',relationship:'diverged',
      files:[file('PercLib/gone.lean','gone',5), file('PercLib/same.lean','old-body',3)]}};
  const rows = parseSimpleCsv(fileHistoryCsv(history));
  assert.deepEqual(rows.map(r=>[r.path,r.state,r.leanLinesReference,r.leanLinesSelected,r.leanLinesDelta]),[
    ['PercLib/gone.lean','Removed','5','0','-5'],
    ['PercLib/new.lean','Added','0','7','7'],
    ['PercLib/same.lean','Modified','3','3','0'],
  ]);
  assert.ok(rows.every(r=>r.referenceInventoryAvailable==='true' && r.referenceCommit==='base' && r.referenceRelationship==='diverged' && r.articleWordsDelta===''));
  assert.equal(rows[2].referenceBlob,'old-body');assert.equal(rows[2].selectedBlob,'new-body');
});

test('file CSV distinguishes unavailable inventories and counters from absent files', () => {
  const file={path:'wiki/sources/map.md',blob:'map',kind:'reading-map',counts:{readingMapWords:12}};
  const history={available:true,tip:'tip',shallow:true,files:[file],comparison:{available:true,referenceCommit:'base',relationship:'ahead'}};
  let [row]=parseSimpleCsv(fileHistoryCsv(history));
  assert.equal(row.state,'Reference unavailable');assert.equal(row.referenceInventoryAvailable,'false');
  assert.equal(row.readingMapWordsReference,'');assert.equal(row.readingMapWordsDelta,'');assert.equal(row.readingMapWordsSelected,'12');
  history.comparison.files=[{...file,counts:{}}];
  [row]=parseSimpleCsv(fileHistoryCsv(history));
  assert.equal(row.state,'Unchanged');assert.equal(row.readingMapWordsReference,'');assert.equal(row.readingMapWordsDelta,'');
  assert.equal(fileHistoryCsv({available:true}),null);
  assert.equal(fileHistoryCsv({available:false,files:[]}),null);
  assert.equal(fileHistoryCsv({available:true,tip:'empty',shallow:false,files:[]}).trimEnd().split('\r\n').length,1);
});

test('file CSV quotes source paths containing commas, quotes and line breaks', () => {
  const history={available:true,tip:'tip',shallow:false,files:[{path:'wiki/articles/a,"b\nc.md',blob:'blob',kind:'article',counts:{articleWords:1}}]};
  assert.ok(fileHistoryCsv(history).includes('"wiki/articles/a,""b\nc.md"'));
});
