import { add, neighbors, remove, theta } from "./theta-search.mjs";
import { distances, ruledOutByForcedPurchases } from "./forced-block-purchases.mjs";
import { chainAttachmentExcess } from "./chain-attachments.mjs";

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

// Each two-step geodesic destination saves at least one unit. In the
// worst case, all extra vertices attach to the skipped vertex.
function hasUniformTwoStepSwap(adj, orders, extras) {
  const degreeTwo = adj.map(row => {
    const adjacent = [...neighbors(row)];
    return adjacent.length === 2 ? adjacent : null;
  });
  function profitable(from, target) {
    if (adj[from] & (1 << target)) return false;
    let improved = 0;
    for (let x = 0; x < adj.length; x++) {
      if (orders[from][x] === 2 + orders[target][x]) improved++;
      if (improved > 1 + extras) return true;
    }
    return false;
  }
  for (let u = 0; u < adj.length; u++) {
    const two = degreeTwo[u];
    if (!two) continue;
    for (const v of two) {
      if (u >= v || !degreeTwo[v]) continue;
      const back = two[0] === v ? two[1] : two[0];
      const next = degreeTwo[v][0] === u ? degreeTwo[v][1] : degreeTwo[v][0];
      if (profitable(u, next) && profitable(v, back)) return true;
    }
  }
  return false;
}

function checkWeights(adj, orders, extras, stats) {
  if (hasUniformTwoStepSwap(adj, orders, extras)) {
    stats.uniformTwoStepRefutations++;
    return;
  }
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
    if (coversAll(first, remaining)) return;
    if (remaining === 0)
      throw Error(JSON.stringify({ adj, changes, uncovered: true }));
    // The final weight takes all remaining vertices.
    const minimum = first === adj.length - 1 ? remaining : 0;
    for (let count = minimum; count <= remaining; count++) {
      changes[first] = count;
      for (const move of moves) move.gain += count * move.scores[first];
      visit(first + 1, remaining - count);
      for (const move of moves) move.gain -= count * move.scores[first];
    }
    changes[first] = 0;
  }
  visit(0, extras);
}

// Intern the sorted lengths of parallel paths. The identifiers only need
// to be consistent within a run. A single path uses its own length.
const parallelLabels = new Map();
function lengthLabel(lengths) {
  if (!lengths) return 0;
  if (lengths.length === 1) return lengths[0];
  const key = lengths.sort((a, b) => a - b).join(",");
  if (!parallelLabels.has(key)) parallelLabels.set(key, 31 + parallelLabels.size);
  return parallelLabels.get(key);
}

function matrixCode(keys, order) {
  // Store only labelled edges above the diagonal. The vertex count and
  // fixed-width records preserve exact equality of the ordered matrices.
  const characters = [order.length];
  for (let i = 0; i < order.length; i++) {
    for (let j = i + 1; j < order.length; j++) {
      const code = keys[order[i]][order[j]];
      if (!code) continue;
      characters.push(i, j, code >>> 24, (code >>> 16) & 255, (code >>> 8) & 255, code & 255);
    }
  }
  return String.fromCharCode(...characters);
}

function canonicalMatrix(keys, vertices) {
  const size = keys.length;
  const radix = 0x100000000;
  function refine(colors) {
    let colorCount = new Set(colors).size;
    while (colorCount < size) {
      const signatures = keys.map((row, i) => {
        const adjacent = [];
        for (let j = 0; j < size; j++) {
          if (row[j]) adjacent.push(colors[j] * radix + row[j]);
        }
        adjacent.sort((a, b) => a - b);
        const characters = [colors[i]];
        for (const pair of adjacent) {
          const label = pair % radix;
          characters.push(Math.floor(pair / radix), label >>> 16, label & 0xffff);
        }
        return String.fromCharCode(...characters);
      });
      const types = [...new Set(signatures)].sort();
      const ranks = new Map(types.map((type, i) => [type, i]));
      colors = signatures.map(type => ranks.get(type));
      if (types.length === colorCount) break;
      colorCount = types.length;
    }
    return colors;
  }
  function label(seed) {
    const colors = refine(seed);
    const classes = Array.from({ length: size + 1 }, () => []);
    for (const i of vertices) classes[colors[i]].push(i);
    const tied = classes.find(group => group.length > 1);
    if (!tied) {
      const order = vertices.slice().sort((i, j) => colors[i] - colors[j]);
      return matrixCode(keys, order);
    }
    let best;
    for (const chosen of tied) {
      const individual = colors.slice();
      individual[chosen] = size;
      const candidate = label(individual);
      if (best === undefined || candidate < best) best = candidate;
    }
    return best;
  }
  return label(vertices.map(() => 0));
}

// Suppressing the degree-two vertices gives paths whose lengths label the
// edges of a multigraph. Different orders on the branch vertices are handled
// by canonicalMatrix.
function encodeBlock(adj, twoLayers) {
  const degrees = adj.map(bits => {
    let degree = 0;
    for (; bits; bits &= bits - 1) degree++;
    return degree;
  });
  const unvisited = adj.slice();
  const branch = [];
  const ids = new Int8Array(adj.length).fill(-1);
  for (let u = 0; u < adj.length; u++) {
    if (degrees[u] <= 2) continue;
    ids[u] = branch.length;
    branch.push(u);
  }
  const matrix = branch.map(() => Array(branch.length).fill(null));
  const chains = [];
  let attachmentBudget = 0;
  for (let i = 0; i < branch.length; i++) {
    const u = branch[i];
    for (let bits = unvisited[u]; bits; bits &= bits - 1) {
      let previous = u, current = 31 - Math.clz32(bits & -bits);
      let length = 1, interior = 0;
      while (degrees[current] === 2) {
        interior |= 1 << current;
        const nextVertex = 31 - Math.clz32(adj[current] & ~(1 << previous));
        previous = current;
        current = nextVertex;
        length++;
      }
      const j = ids[current];
      // The other endpoint will not traverse this path in reverse.
      unvisited[current] &= ~(1 << previous);
      const excess = chainAttachmentExcess(length, degrees[u], degrees[current], twoLayers);
      attachmentBudget += excess;
      if (excess) chains.push({ interior, excess });
      const lengths = matrix[i][j];
      if (lengths) lengths.push(length);
      else matrix[i][j] = matrix[j][i] = [length];
    }
  }
  return { matrix, chains, attachmentBudget };
}

function reachesBlockWithin(adj, root, steps) {
  const all = (1 << adj.length) - 1;
  let frontier = 1 << root;
  let reached = frontier;
  for (let step = 0; step < steps; step++) {
    let adjacent = 0;
    for (let bitset = frontier; bitset; bitset &= bitset - 1)
      adjacent |= adj[31 - Math.clz32(bitset & -bitset)];
    frontier = adjacent & ~reached;
    reached |= frontier;
    if (reached === all) return true;
  }
  return false;
}

// If the eccentricity plus the available vertices plus one is below the
// girth, no continuation can use the vertex as an endpoint of a new ear.
function canPruneExtensions(adj, chains, extras, girth) {
  const steps = girth - extras - 2;
  if (steps < 1) return false;
  let budget = 0;
  for (const { interior, excess } of chains) {
    let remaining = interior;
    for (; remaining; remaining &= remaining - 1) {
      const u = 31 - Math.clz32(remaining & -remaining);
      if (!reachesBlockWithin(adj, u, steps)) break;
    }
    if (remaining) continue;
    budget += excess;
    if (budget > extras) return true;
  }
  return false;
}

function searchBlocks(girth, maxOrder, pruneExtensions, twoLayers, repairEars) {
  const seen = new Set();
  const seenOrdered = new Set();
  const stats = { girth, maxOrder, blocks: {}, chainWeightRefutations: 0,
    uniformTwoStepRefutations: 0, orientationRefutations: 0, weightBranches: 0 };
  if (pruneExtensions) stats.prunedExtensions = 0;
  if (repairEars) stats.restrictedExtensions = 0;
  function visit(adj) {
    const { matrix, chains, attachmentBudget } = encodeBlock(adj, twoLayers);
    const keys = matrix.map(row => row.map(lengthLabel));
    const vertices = Array.from({ length: keys.length }, (_, i) => i);
    const ordered = matrixCode(keys, vertices);
    // Keep a bounded cache of unchanged vertex orderings. Clearing it
    // only costs an opportunity to skip a canonicalization.
    if (seenOrdered.has(ordered)) return;
    if (seenOrdered.size === 262144) seenOrdered.clear();
    seenOrdered.add(ordered);
    const n = adj.length;
    const extras = maxOrder - n;
    if (pruneExtensions && attachmentBudget > extras && canPruneExtensions(adj, chains, extras, girth)) {
      stats.prunedExtensions++;
      return;
    }
    const key = canonicalMatrix(keys, vertices);
    if (seen.has(key)) return;
    seen.add(key);
    stats.blocks[n] = (stats.blocks[n] ?? 0) + 1;
    const d = adj.map((_, u) => distances(adj, u));
    if (attachmentBudget > extras)
      stats.chainWeightRefutations++;
    else
      checkWeights(adj, d, extras, stats);
    let needsEar = 0;
    if (repairEars && attachmentBudget > extras) {
      // At least one interior in a group whose excess exceeds the budget
      // must acquire an edge. Two-connectivity lets an ear using that edge
      // be added first, even when its other endpoint is new in the final block.
      let excess = 0;
      for (const chain of chains.sort((a, b) => b.excess - a.excess)) {
        excess += chain.excess;
        needsEar |= chain.interior;
        if (excess > extras) break;
      }
      stats.restrictedExtensions++;
    }
    for (let u = 0; u < n; u++) {
      for (let v = u + 1; v < n; v++) {
        if (needsEar && !(needsEar & ((1 << u) | (1 << v)))) continue;
        // The shortest new cycle uses the old shortest path between the ends.
        const first = Math.max(1, girth - d[u][v], (adj[u] & (1 << v)) ? 2 : 1);
        for (let length = first; length <= maxOrder - n + 1; length++) {
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

const maxOrder = Number(process.argv[2] ?? 26);
if (!Number.isInteger(maxOrder) || maxOrder < 13 || maxOrder > 30)
  throw Error("Choose an integer order between 13 and 30");
const pruneExtensions = process.argv.includes("--prune-extensions");
const twoLayers = process.argv.includes("--two-layer-bounds");
const repairEars = process.argv.includes("--repair-ears");
console.log(JSON.stringify(searchBlocks(9, maxOrder, pruneExtensions, twoLayers, repairEars), null, 2));
