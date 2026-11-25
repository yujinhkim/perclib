import fs from "node:fs/promises";
import path from "node:path";

// Catalogs describe sources and subjects. Article-owned records supply their
// memberships and relations, so adding an article never edits another's rows.
export function assembleRecords(catalog, records, articles, assertions) {
  const sources = structuredClone(catalog.sources);
  const collections = structuredClone(catalog.collections);
  const bySource = new Map(sources.map((s) => [s.id, s]));
  const byCollection = new Map(collections.map((c) => [c.id, c]));
  const byArticle = new Map(articles.map((a) => [a.id, a]));
  const owners = new Map(assertions.map((a) => [a.tag, a.article]));
  const seen = new Set(), occurrences = [], proofUses = [];
  if (bySource.size !== sources.length || byCollection.size !== collections.length)
    throw Error("Records: duplicate source or collection");
  for (const source of sources) {
    if ("occurrences" in source) throw Error("Records: source rows belong to articles");
    source.occurrences = [];
  }
  for (const collection of collections) {
    if ("pages" in collection) throw Error("Records: collection memberships belong to articles");
    collection.pages = [];
  }
  const ordered = (rows) => rows.sort((a, b) => a.order - b.order || a.owner.localeCompare(b.owner));
  const rowOrder = (row) => {
    if (!Number.isSafeInteger(row.order) || row.order < 0)
      throw Error("Records: invalid display order");
  };
  for (const record of records) {
    if (record.schema !== "perclib-article-records-v1" ||
        !byArticle.has(record.article) || seen.has(record.article) ||
        ["collections", "sourceOccurrences", "occursIn", "proofUses"].some((k) => !Array.isArray(record[k])))
      throw Error("Records: invalid or duplicate article record");
    seen.add(record.article);
    const memberships = new Set();
    for (const row of record.collections) {
      rowOrder(row);
      if (!byCollection.has(row.collection) || memberships.has(row.collection))
        throw Error("Records: unknown or duplicate collection membership");
      memberships.add(row.collection);
      byCollection.get(row.collection).pages.push({order: row.order, owner: record.article});
    }
    for (const row of record.sourceOccurrences) {
      rowOrder(row);
      const {source, order, ...occurrence} = row;
      if (!bySource.has(source) || "pageId" in occurrence)
        throw Error("Records: unknown source or foreign editorial owner");
      bySource.get(source).occurrences.push({order, owner: record.article,
        value: {...occurrence, pageId: record.article}});
    }
    for (const [key, destination] of [["occursIn", occurrences], ["proofUses", proofUses]]) {
      for (const row of record[key]) {
        rowOrder(row);
        const {order, ...value} = row;
        if (owners.get(value.tag) !== record.article)
          throw Error(`Records: ${value.tag} does not belong to ${record.article}`);
        destination.push({order, owner: record.article, value});
      }
    }
  }
  for (const collection of collections)
    collection.pages = ordered(collection.pages).map((row) => row.owner);
  for (const source of sources)
    source.occurrences = ordered(source.occurrences).map((row) => row.value);
  return {sources, collections,
    occursIn: {schema: "perclib-occurs-in-v1", occurrences: ordered(occurrences).map((row) => row.value)},
    proofUses: {schema: "perclib-proof-uses-v1", assertions: ordered(proofUses).map((row) => row.value)}};
}

export async function loadRecords(root, articles, assertions) {
  for (const legacy of ["src/content/editorial.json", "relations/occurs-in.json", "relations/proof-uses.json"]) {
    try {
      await fs.access(path.join(root, legacy));
    } catch (error) {
      if (error.code === "ENOENT") continue;
      throw error;
    }
    throw Error(`Records: migrate legacy shared file ${legacy} before building`);
  }
  const catalog = JSON.parse(await fs.readFile(path.join(root, "src/content/catalog.json"), "utf8"));
  const directory = path.join(root, "records");
  const names = (await fs.readdir(directory)).filter((name) => name.endsWith(".json")).sort();
  const records = await Promise.all(names.map(async (name) => {
    const record = JSON.parse(await fs.readFile(path.join(directory, name), "utf8"));
    if (name !== `${record.article}.json`) throw Error("Records: filename must match article owner");
    return record;
  }));
  return assembleRecords(catalog, records, articles, assertions);
}
