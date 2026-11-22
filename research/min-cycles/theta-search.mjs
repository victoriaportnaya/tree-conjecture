import { pathToFileURL } from "node:url";

function theta(lengths) {
  const edges = [];
  let order = 2;
  for (const length of lengths) {
    const path = [0];
    for (let step = 1; step < length; step++) path.push(order++);
    path.push(1);
    for (let i = 1; i < path.length; i++) edges.push([path[i - 1], path[i]]);
  }
  return { edges, order };
}

function distanceSum(adj, root) {
  let frontier = 1 << root;
  let visited = frontier;
  let sum = 0;
  for (let d = 0; frontier; d++) {
    let next = 0;
    for (let layer = frontier; layer; layer &= layer - 1) {
      const vertex = 31 - Math.clz32(layer & -layer);
      next |= adj[vertex];
      sum += d;
    }
    frontier = next & ~visited;
    visited |= frontier;
  }
  return visited === (1 << adj.length) - 1 ? sum : Infinity;
}

function close(adj, root, vertex, bound) {
  let frontier = 1 << root;
  let visited = frontier;
  for (let d = 0; frontier && d < bound; d++) {
    if (frontier & (1 << vertex)) return true;
    let next = 0;
    for (let layer = frontier; layer; layer &= layer - 1)
      next |= adj[31 - Math.clz32(layer & -layer)];
    frontier = next & ~visited;
    visited |= frontier;
  }
  return false;
}

function* neighbors(mask) {
  for (; mask; mask &= mask - 1) yield 31 - Math.clz32(mask & -mask);
}

function add(adj, u, v) {
  adj[u] |= 1 << v;
  adj[v] |= 1 << u;
}

function remove(adj, u, v) {
  adj[u] &= ~(1 << v);
  adj[v] &= ~(1 << u);
}

function bestSwap(adj, priorSum, buyer, sold) {
  remove(adj, buyer, sold);
  let best = 0;
  for (let link = 0; link < adj.length; link++) {
    if (link === buyer || link === sold || (adj[buyer] & (1 << link))) continue;
    add(adj, buyer, link);
    const change = distanceSum(adj, buyer) - priorSum;
    best = Math.min(best, change);
    remove(adj, buyer, link);
  }
  add(adj, buyer, sold);
  return best;
}

function ruledOutByBothBuyers(adj) {
  const totals = adj.map((_, root) => distanceSum(adj, root));
  for (let u = 0; u < adj.length; u++) {
    for (const v of neighbors(adj[u])) {
      if (u >= v) continue;
      if (bestSwap(adj, totals[u], u, v) < 0 && bestSwap(adj, totals[v], v, u) < 0)
        return true;
    }
  }
  return false;
}

function checkExtensions(lengths, n, girth) {
  const { edges, order } = theta(lengths);
  const adj = Array(n).fill(0);
  for (const [u, v] of edges) add(adj, u, v);
  const candidates = [];
  for (let u = 0; u < n; u++)
    for (let v = u + 1; v < n; v++)
      if (!(adj[u] & (1 << v))) candidates.push([u, v]);

  let connected = 0;
  function search(start) {
    if (Number.isFinite(distanceSum(adj, 0))) {
      connected++;
      if (!ruledOutByBothBuyers(adj)) {
        throw Error(JSON.stringify({ lengths, n, graph: adj.map(ns => [...neighbors(ns)]) }));
      }
    }
    for (let i = start; i < candidates.length; i++) {
      const [u, v] = candidates[i];
      if (close(adj, u, v, girth - 1)) continue;
      add(adj, u, v);
      search(i + 1);
      remove(adj, u, v);
    }
  }
  search(0);
  return connected;
}

function run(girth, maxOrder) {
  const totals = {};
  const seeds = {};
  for (let a = 1; 3 * a <= maxOrder + 1; a++) {
    for (let b = a; a + 2 * b <= maxOrder + 1; b++) {
      if (a + b < girth) continue;
      for (let c = b; a + b + c <= maxOrder + 1; c++) {
        for (let n = a + b + c - 1; n <= maxOrder; n++) {
          totals[n] = (totals[n] ?? 0) + checkExtensions([a, b, c], n, girth);
          seeds[n] = (seeds[n] ?? 0) + 1;
        }
      }
    }
  }
  return { girth, maxOrder, totals, seeds };
}

export { add, close, neighbors, remove, theta };

function main() {
  const requestedGirth = process.argv[2] ?? "7";
  const configurations = {
    "7": { maxOrder: 15, totals: { 10: 1, 11: 13, 12: 167, 13: 2671, 14: 53452, 15: 1318078 } },
    "8": { maxOrder: 16, totals: { 11: 1, 12: 13, 13: 171, 14: 2624, 15: 48226, 16: 1061903 } },
    "9": { maxOrder: 18, totals: { 13: 1, 14: 16, 15: 242, 16: 4116, 17: 80290, 18: 1802085 } },
  };
  if (!Object.hasOwn(configurations, requestedGirth)) {
    throw Error("Choose minimum cycle length 7, 8 or 9");
  }
  const expected = configurations[requestedGirth];
  const result = run(Number(requestedGirth), expected.maxOrder);
  if (JSON.stringify(result.totals) !== JSON.stringify(expected.totals)) {
    throw Error("Unexpected enumeration counts");
  }
  console.log(JSON.stringify(result, null, 2));
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) main();
