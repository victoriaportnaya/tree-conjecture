import { readFileSync } from "node:fs";

function adjacency(profile) {
  const n = profile.length;
  const adj = Array.from({ length: n }, () => Array(n).fill(false));
  for (let u = 0; u < n; u++) {
    if (!Array.isArray(profile[u])) throw new Error("Each strategy must be an array");
    for (const v of profile[u]) {
      if (!Number.isInteger(v) || v < 0 || v >= n || u === v || adj[u][v])
        throw new Error("Expected a simple graph with one buyer per edge");
      adj[u][v] = adj[v][u] = true;
    }
  }
  return adj;
}

function distances(adj, root, removed = -1) {
  const d = Array(adj.length).fill(-1);
  const queue = [root];
  d[root] = 0;
  for (let i = 0; i < queue.length; i++) {
    const u = queue[i];
    for (let v = 0; v < adj.length; v++) {
      if (v === removed || !adj[u][v] || d[v] !== -1) continue;
      d[v] = d[u] + 1;
      queue.push(v);
    }
  }
  return d;
}

function* subsets(vertices, next = 0, selected = []) {
  if (next === vertices.length) {
    yield selected;
    return;
  }
  yield* subsets(vertices, next + 1, selected);
  selected.push(vertices[next]);
  yield* subsets(vertices, next + 1, selected);
  selected.pop();
}

// Rows use [edge-count change, distance change at each vertex].
function deviationRows(profile, adj, before) {
  const rows = [];
  for (let u = 0; u < profile.length; u++) {
    const available = profile.flatMap((p, v) => v !== u && !p.includes(u) ? [v] : []);
    for (const selected of subsets(available)) {
      for (const v of profile[u]) adj[u][v] = adj[v][u] = false;
      for (const v of selected) adj[u][v] = adj[v][u] = true;
      const after = distances(adj, u);
      for (const v of selected) adj[u][v] = adj[v][u] = false;
      for (const v of profile[u]) adj[u][v] = adj[v][u] = true;
      if (after.includes(-1)) continue;
      const row = [selected.length - profile[u].length, ...after.map((d, v) => d - before[u][v])];
      if (row.some(x => x !== 0)) rows.push(row);
    }
  }
  return rows;
}

function blockRows(profile, active) {
  const adj = adjacency(profile);
  const n = adj.length;
  if (n < 3) throw new Error("A cyclic block has at least three vertices");
  const d = adj.map((_, u) => distances(adj, u));
  for (let removed = 0; removed < n; removed++) {
    const dWithout = distances(adj, removed === 0 ? 1 : 0, removed);
    if (dWithout.some((value, v) => v !== removed && value < 0))
      throw new Error("The core must be two-connected");
  }
  const rows = deviationRows(profile, adj, d);
  for (const v of active) {
    if (!Number.isInteger(v) || v < 0 || v >= n) throw new Error("Invalid leaf support");
    for (let r = 0; r < n; r++) {
      if (r === v) continue;
      rows.push([1, ...d[v].map((value, z) => -Math.max(0, value - d[r][z]))]);
    }
  }
  return rows;
}

function linearExpression(coefficients, names) {
  return coefficients.flatMap((c, i) =>
    c === 0 ? [] : [`${c < 0 ? "-" : "+"} ${Math.abs(c)} ${names[i]}`]
  ).join(" ").replace(/^\+ /, "") || "0";
}

function buildBlockMILP(profile, active) {
  const rows = blockRows(profile, active);
  const weights = profile.map((_, v) => `w_${v}`);
  const names = ["alpha", ...weights];
  const gap = profile.length - 1;
  const lines = ["Minimize", ` total: ${weights.join(" + ")}`, "Subject To"];
  rows.forEach((row, i) => lines.push(` c${i}: ${linearExpression(row, names)} >= 0`));
  lines.push(` gap: ${linearExpression([gap, ...weights.map(() => -gap)], names)} >= 1`);
  lines.push("Bounds", " 0 <= alpha");
  weights.forEach((w, v) => lines.push(active.includes(v) ? ` 2 <= ${w}` : ` ${w} = 1`));
  lines.push("Generals", ` ${weights.join(" ")}`, "End");
  return lines.join("\n") + "\n";
}

const { profile, active } = JSON.parse(readFileSync(0, "utf8"));
process.stdout.write(buildBlockMILP(profile, active));
