import { pathToFileURL } from "node:url";
import { add, neighbors, theta } from "./theta-search.mjs";

export function distances(adj, root) {
  const d = Array(adj.length).fill(Infinity);
  d[root] = 0;
  const queue = [root];
  for (const u of queue) {
    for (const v of neighbors(adj[u])) {
      if (d[v] !== Infinity) continue;
      d[v] = d[u] + 1;
      queue.push(v);
    }
  }
  return d;
}

/** Refute all positive attachment weights using a maximum-weight vertex. */
export function ruledOutByForcedPurchases(adj, d) {
  const n = adj.length;
  const vertices = adj.map(row => [...neighbors(row)]);
  const triples = [];
  const consequences = Array.from({ length: n * n }, () => []);
  const ownership = (buyer, target) => buyer * n + target;
  const reverse = direction => (direction % n) * n + Math.floor(direction / n);

  for (let b = 0; b < n; b++) {
    if (vertices[b].length !== 2) continue;
    const [left, right] = vertices[b];
    for (const [a, c] of [[left, right], [right, left]]) {
      triples.push([a, b, c]);
      if (vertices[c].length !== 2) continue;
      const end = vertices[c].find(v => v !== b);
      if (d[a][end] !== 3) continue;
      // One inward purchase excludes the other inward purchase.
      consequences[ownership(a, b)].push(ownership(c, end));
      consequences[ownership(end, c)].push(ownership(b, a));
    }
  }

  for (let x = 0; x < n; x++) {
    const queue = [];
    for (const [a, b, c] of triples) {
      if (c !== x && d[a][x] === d[c][x] + 2) queue.push(ownership(b, a));
    }
    const forced = new Uint8Array(n * n);
    let contradiction = false;
    for (const direction of queue) {
      if (forced[direction]) continue;
      if (forced[reverse(direction)]) {
        contradiction = true;
        break;
      }
      forced[direction] = 1;
      queue.push(...consequences[direction]);
    }
    if (!contradiction) return false;
  }
  return true;
}

function checkThetaFamilies(girth, maxOrder) {
  let excluded = 0, inconclusive = 0;
  for (let a = 1; 3 * a <= maxOrder + 1; a++) {
    for (let b = a; a + 2 * b <= maxOrder + 1; b++) {
      if (a + b < girth) continue;
      for (let c = b; a + b + c <= maxOrder + 1; c++) {
        const { edges, order } = theta([a, b, c]);
        const adj = Array(order).fill(0);
        for (const [u, v] of edges) add(adj, u, v);
        const d = adj.map((_, i) => distances(adj, i));
        const result = ruledOutByForcedPurchases(adj, d);
        if (!result && b >= a + 4)
          throw Error(JSON.stringify({ a, b, c, message: "Long theta theorem regression" }));
        if (result) excluded++;
        else inconclusive++;
      }
    }
  }
  return { girth, maxOrder, excluded, inconclusive };
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) {
  const maxOrder = Number(process.argv[2] ?? 30);
  if (!Number.isInteger(maxOrder) || maxOrder < 13 || maxOrder > 30)
    throw Error("Choose an integer order between 13 and 30");
  console.log(JSON.stringify(checkThetaFamilies(9, maxOrder), null, 2));
}
