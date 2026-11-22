import { add, close, neighbors, remove, theta } from "./theta-search.mjs";

import { distances, ruledOutByForcedPurchases } from "./forced-block-purchases.mjs";

function swapGains(adj, from, to, before) {
  const gains = [];
  remove(adj, from, to);
  for (let target = 0; target < adj.length; target++) {
    if (target === from || target === to || (adj[from] & (1 << target))) continue;
    add(adj, from, target);
    const after = distances(adj, from);
    remove(adj, from, target);
    if (!after.every(Number.isFinite)) continue;
    const scores = before.map((old, i) => old - after[i]);
    const base = scores.reduce((a, b) => a + b, 0);
    const worst = Array(scores.length + 1).fill(Infinity);
    for (let i = scores.length - 1; i >= 0; i--)
      worst[i] = Math.min(scores[i], worst[i + 1]);
    gains.push({ scores, worst, gain: base });
  }
  add(adj, from, to);
  return gains;
}

function checkWeights(adj, extras, stats) {
  const orders = adj.map((_, i) => distances(adj, i));
  if (ruledOutByForcedPurchases(adj, orders)) {
    stats.orientationRefutations++;
    return;
  }
  const edges = [];
  const moves = [];
  const profitable = (options, first, remaining) =>
    options.some(move => move.gain + remaining * Math.min(0, move.worst[first]) > 0);
  for (let u = 0; u < adj.length; u++) {
    for (const v of neighbors(adj[u])) {
      if (u >= v) continue;
      const forward = swapGains(adj, u, v, orders[u]);
      const reverse = swapGains(adj, v, u, orders[v]);
      if (!forward.length || !reverse.length) continue;
      if (profitable(forward, 0, extras) && profitable(reverse, 0, extras)) {
        stats.weightBranches++;
        return;
      }
      edges.push([forward, reverse]);
      moves.push(...forward, ...reverse);
    }
  }
  const changes = Array(adj.length).fill(0);
  function coversAll(first, remaining) {
    return edges.some(([forward, reverse]) =>
      profitable(forward, first, remaining) && profitable(reverse, first, remaining));
  }
  function visit(first, remaining) {
    stats.weightBranches++;
    // Each remaining vertex may add to any one of the remaining block weights.
    if (coversAll(first, remaining)) return;
    if (remaining === 0 || first === adj.length)
      throw Error(JSON.stringify({ adj, changes, uncovered: true }));
    for (let count = 0; count <= remaining; count++) {
      changes[first] = count;
      for (const move of moves) move.gain += count * move.scores[first];
      visit(first + 1, remaining - count);
      for (const move of moves) move.gain -= count * move.scores[first];
    }
    changes[first] = 0;
  }
  visit(0, extras);
}

// A key specifies a length-labelled multigraph obtained by suppressing degree-two
// vertices. Equality of keys implies isomorphism, even when tied vertices end up
// in different orders and two isomorphic blocks therefore receive different keys.
function blockKey(adj) {
  const neighborLists = adj.map(row => [...neighbors(row)]);
  const branch = neighborLists.map((row, u) => row.length > 2 ? u : -1).filter(u => u >= 0);
  const ids = new Map(branch.map((u, i) => [u, i]));
  const matrix = branch.map(() => branch.map(() => []));
  for (const [i, u] of branch.entries()) {
    for (const first of neighborLists[u]) {
      let previous = u, current = first, length = 1;
      while (neighborLists[current].length === 2) {
        const [a, b] = neighborLists[current];
        [previous, current] = [current, a === previous ? b : a];
        length++;
      }
      matrix[i][ids.get(current)].push(length);
    }
  }
  const lengthKey = row => row.sort((a, b) => a - b).join(",");
  const keys = matrix.map(row => row.map(lengthKey));
  const signatures = keys.map(row => row.filter(Boolean).sort().join(";"));
  const order = branch.map((_, i) => i).sort((i, j) => {
    const a = signatures[i], b = signatures[j];
    return a < b ? -1 : a > b ? 1 : i - j;
  });
  return order.map(i => order.map(j => keys[i][j]).join(":")).join("|");
}

function searchBlocks(girth, maxOrder) {
  const seen = new Set();
  const stats = { girth, maxOrder, blocks: {}, orientationRefutations: 0, weightBranches: 0 };
  function visit(adj) {
    const key = blockKey(adj);
    if (seen.has(key)) return;
    seen.add(key);
    const n = adj.length;
    stats.blocks[n] = (stats.blocks[n] ?? 0) + 1;
    checkWeights(adj, maxOrder - n, stats);
    for (let u = 0; u < n; u++) {
      for (let v = u + 1; v < n; v++) {
        for (let length = 1; length <= maxOrder - n + 1; length++) {
          if (length === 1 && (adj[u] & (1 << v))) continue;
          // Every new cycle consists of this ear and a path between its endpoints.
          if (close(adj, u, v, girth - length)) continue;
          let previous = u;
          for (let x = n; x < n + length - 1; x++) {
            adj.push(0);
            add(adj, previous, x);
            previous = x;
          }
          add(adj, previous, v);
          visit(adj);
          remove(adj, previous, v);
          for (let x = n + length - 2; x >= n; x--) {
            remove(adj, x === n ? u : x - 1, x);
            adj.pop();
          }
        }
      }
    }
  }
  for (let a = 1; 3 * a <= maxOrder + 1; a++) {
    for (let b = a; a + 2 * b <= maxOrder + 1; b++) {
      if (a + b < girth) continue;
      for (let c = b; a + b + c <= maxOrder + 1; c++) {
        const { edges, order } = theta([a, b, c]);
        const adj = Array(order).fill(0);
        for (const [u, v] of edges) add(adj, u, v);
        visit(adj);
      }
    }
  }
  return stats;
}

const maxOrder = Number(process.argv[2] ?? 24);
if (!Number.isInteger(maxOrder) || maxOrder < 13 || maxOrder > 30)
  throw Error("Choose an integer order between 13 and 30");
console.log(JSON.stringify(searchBlocks(9, maxOrder), null, 2));
