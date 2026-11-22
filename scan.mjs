function* members(mask) {
  while (mask) {
    const bit = mask & -mask;
    yield 31 - Math.clz32(bit);
    mask ^= bit;
  }
}

function count(mask) {
  let size = 0;
  while (mask) {
    mask &= mask - 1;
    size++;
  }
  return size;
}

function distanceSum(adjacency, start) {
  const distances = Array(adjacency.length).fill(-1);
  const queue = [start];
  distances[start] = 0;
  let sum = 0;
  for (const vertex of queue) {
    for (const neighbor of members(adjacency[vertex])) {
      if (distances[neighbor] !== -1) continue;
      distances[neighbor] = distances[vertex] + 1;
      sum += distances[neighbor];
      queue.push(neighbor);
    }
  }
  return queue.length === adjacency.length ? sum : null;
}

function replaceIncidentEdges(adjacency, player, neighbors) {
  const playerBit = 1 << player;
  return adjacency.map((row, vertex) => {
    if (vertex === player) return neighbors;
    const unchanged = row & ~playerBit;
    return neighbors & (1 << vertex) ? unchanged | playerBit : unchanged;
  });
}

function* alternatives(owned, available, mode) {
  if (mode === "delete") {
    for (const target of members(owned)) yield owned ^ (1 << target);
  } else if (mode === "swap") {
    for (const added of members(available & ~owned)) {
      yield owned | (1 << added);
      for (const dropped of members(owned)) {
        yield (owned ^ (1 << dropped)) | (1 << added);
      }
    }
  } else {
    // All remaining strategies delete or add at least two targets.
    for (let targets = available; ; targets = (targets - 1) & available) {
      if (count(owned & ~targets) > 1 || count(targets & ~owned) > 1) {
        yield targets;
      }
      if (targets === 0) break;
    }
  }
}

function testOrientation(adjacency, before, ownership, threshold) {
  const modes = ["delete", "swap", "all"];
  const playersMask = (1 << adjacency.length) - 1;
  let lower = null;
  let upper = null;
  for (const mode of modes) {
    for (const [player, owned] of ownership.entries()) {
      const incoming = adjacency[player] & ~owned;
      const available = playersMask & ~(incoming | (1 << player));
      for (const targets of alternatives(owned, available, mode)) {
        const modified = replaceIncidentEdges(adjacency, player, targets | incoming);
        const after = distanceSum(modified, player);
        if (after === null) continue;

        const a = count(targets) - count(owned);
        const b = after - before[player];
        const witness = {player, targets, a, b};
        if (a === 0 && b < 0) return {mode, witnesses: [witness]};

        // An addition gives alpha >= -b/a. A deletion gives alpha <= b/(-a).
        if (a > 0 && (!lower || -b * lower.a > -lower.b * a)) lower = witness;
        if (a < 0 && (!upper || b * (-upper.a) < upper.b * (-a))) upper = witness;
        if (upper && upper.b <= threshold * (-upper.a)) return {mode, witnesses: [upper]};
        if (upper && lower && upper.b * lower.a < -lower.b * (-upper.a)) {
          return {mode, witnesses: [lower, upper]};
        }
      }
    }
  }
  return null;
}

function edgeRelabellings(n, edges, edgeIndex) {
  const maps = [];
  function permute(order, used) {
    if (order.length === n) {
      maps.push(edges.map(([u, v]) => 1 << edgeIndex[order[u]][order[v]]));
      return;
    }
    for (let v = 0; v < n; v++) {
      if (!(used & (1 << v))) permute([...order, v], used | (1 << v));
    }
  }
  permute([], 0);
  return maps;
}

function formatCertificate(ownership, threshold, witnesses) {
  return {
    purchases: ownership.map(mask => Array.from(members(mask))),
    above: String(threshold),
    witnesses: witnesses.map(w => ({...w, targets: Array.from(members(w.targets))})),
  };
}

function scan(n, threshold = n) {
  if (!Number.isInteger(n) || n < 3 || n > 8) throw Error("Expected n from 3 to 8.");
  if (!Number.isSafeInteger(threshold) || threshold < n - 2 || threshold > Math.floor(Number.MAX_SAFE_INTEGER / (n - 1))) {
    throw Error("Expected an integer threshold of at least n - 2 with exact integer arithmetic.");
  }

  const edges = [];
  const edgeIndex = Array.from({length: n}, () => Array(n));
  for (let u = 0; u < n; u++) {
    for (let v = u + 1; v < n; v++) {
      edgeIndex[u][v] = edgeIndex[v][u] = edges.length;
      edges.push([u, v]);
    }
  }
  const adjacency = Array(n).fill(0);
  const seen = new Set();
  const squaresPruned = n === 8;
  const relabellings = edgeRelabellings(n, edges, edgeIndex);
  const totals = {
    n, above: threshold, squaresPruned,
    graphs: 0, profiles: 0, delete: 0, swap: 0, all: 0, survive: 0, examples: {},
  };

  function examine(mask, edgeIds) {
    if (seen.has(mask) || distanceSum(adjacency, 0) === null) return;
    for (const map of relabellings) {
      let image = 0;
      for (const edge of edgeIds) image |= map[edge];
      seen.add(image);
    }
    totals.graphs++;

    const before = adjacency.map((_, player) => distanceSum(adjacency, player));
    for (let orientation = 0; orientation < (1 << edgeIds.length); orientation++) {
      totals.profiles++;
      const ownership = Array(n).fill(0);
      for (const [position, edge] of edgeIds.entries()) {
        const [u, v] = edges[edge];
        if (orientation & (1 << position)) ownership[v] |= 1 << u;
        else ownership[u] |= 1 << v;
      }
      const rejection = testOrientation(adjacency, before, ownership, threshold);
      if (rejection) {
        totals[rejection.mode]++;
        totals.examples[rejection.mode] ??=
          formatCertificate(ownership, threshold, rejection.witnesses);
      } else {
        totals.survive++;
        totals.examples.survive ??= ownership.map(mask => Array.from(members(mask)));
      }
    }
  }

  function generate(next, mask, edgeIds) {
    if (edgeIds.length + edges.length - next < n) return;
    if (next === edges.length) {
      examine(mask, edgeIds);
      return;
    }

    generate(next + 1, mask, edgeIds);
    const [u, v] = edges[next];
    if (adjacency[u] & adjacency[v]) return;
    if (squaresPruned) {
      for (const w of members(adjacency[u])) {
        if (adjacency[w] & adjacency[v]) return;
      }
    }

    adjacency[u] |= 1 << v;
    adjacency[v] |= 1 << u;
    edgeIds.push(next);
    generate(next + 1, mask | (1 << next), edgeIds);
    edgeIds.pop();
    adjacency[u] ^= 1 << v;
    adjacency[v] ^= 1 << u;
  }

  generate(0, 0, []);
  return totals;
}

const n = Number(process.argv[2] ?? 8);
const threshold = Number(process.argv[3] ?? n);
console.log(JSON.stringify(scan(n, threshold), null, 2));
