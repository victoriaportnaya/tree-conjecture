const cuts = {
  "00001101": [
    [11,0,[1],[]], [37,0,[1],[2]], [63,0,[1,7],[3]], [14,0,[1,7],[5]],
    [36,1,[2],[]], [80,1,[2],[3]], [11,1,[2],[4]], [59,2,[3],[]],
    [4,2,[3],[7]], [16,3,[4],[5]], [47,3,[4],[7]], [6,5,[4],[3]],
    [28,6,[5],[4]], [10,6,[5,7],[1]], [31,6,[5,7],[2]]
  ],
  "00011101": [
    [556,0,[1],[2]], [109,0,[1,7],[4]], [225,0,[1,7],[5]], [170,0,[1,7],[6]],
    [244,1,[2],[]], [116,1,[2],[3]], [101,1,[2],[4]], [16,2,[3],[]],
    [91,2,[3],[7]], [109,4,[3],[7]], [204,5,[4],[]], [91,5,[4],[2]],
    [140,5,[4],[3]], [452,6,[5],[4]], [142,6,[5,7],[0]], [279,6,[5,7],[1]],
    [83,6,[5,7],[2]], [8,6,[5,7],[3]]
  ]
};

function ringDistance(i, j) {
  const gap = Math.abs(i - j);
  return Math.min(gap, 8 - gap);
}

function* labelTypes(levels = [0]) {
  if (levels.length === 8) {
    if (Math.abs(levels[7]) <= 1) {
      const minimum = Math.min(...levels);
      yield levels.map(level => level - minimum);
    }
    return;
  }
  for (const step of [-1, 0, 1]) yield* labelTypes([...levels, levels.at(-1) + step]);
}

function certifiedMove(bits, row) {
  const [weight, buyer, sold, added] = row;
  const purchased = [];
  const adj = Array.from({ length: 8 }, () => []);
  function add(u, v) { adj[u].push(v); adj[v].push(u); }
  for (let i = 0; i < 8; i++) {
    const j = (i + 1) % 8;
    const [owner, target] = bits[i] === "0" ? [i, j] : [j, i];
    if (owner === buyer) purchased.push(target);
    if (owner !== buyer || !sold.includes(target)) add(i, j);
  }
  if (!sold.every(j => purchased.includes(j)) || weight < 0 || added.length > sold.length)
    throw Error("Invalid strategy");
  for (const j of added) add(buyer, j);
  const distances = Array(8).fill(Infinity);
  distances[buyer] = 0;
  const queue = [buyer];
  for (const u of queue) for (const v of adj[u]) {
    if (distances[v] !== Infinity) continue;
    distances[v] = distances[u] + 1;
    queue.push(v);
  }
  if (queue.length !== 8) throw Error("Disconnected cycle routes");
  return {weight, buyer, sold, distances, saving: sold.length - added.length};
}

function impact({buyer, sold, distances}, levels) {
  const origin = levels[buyer];
  let bound = sold.every(j => origin !== levels[j] + 1) ? 0 : Infinity;
  for (let j = 0; j < 8; j++) {
    if (levels[j] < origin + ringDistance(buyer, j))
      bound = Math.min(bound, distances[j] + levels[j] - origin);
  }
  if (!Number.isFinite(bound)) throw Error("No certified distance estimate");
  return bound;
}

const all = [...labelTypes()];
if (all.length !== 1107) throw Error("Missing label types");
for (const [bits, rows] of Object.entries(cuts)) {
  const moves = rows.map(row => certifiedMove(bits, row));
  const saving = moves.reduce((acc, move) => acc + move.weight * move.saving, 0);
  const weighted = levels => moves.reduce((acc, move) => acc + move.weight * impact(move, levels), 0);
  const maxOutside = Math.max(...all.map(weighted));
  let onCycle = 0;
  for (let j = 0; j < 8; j++) {
    onCycle += weighted(Array.from({ length: 8 }, (_, i) => ringDistance(i, j)));
  }
  if (!(maxOutside > saving && saving > 0)) throw Error("Invalid price ratio");
  const minimumOrder = Math.floor((8 * maxOutside - onCycle) / (maxOutside - saving)) + 1;
  console.log({ bits, saving, maxOutside, onCycle, minimumOrder });
}

// Outside destinations obey the degree-two identity at any cycle vertex with
// no off-cycle neighbours. The actual eight cycle destinations are kept in T.
const degreeCuts = [
  {
    bits: "00001101", noOutside: [0], withOutside: [],
    rows: [
      [2229,0,[1],[2]], [2798,0,[1,7],[3]], [1236,0,[1,7],[5]], [973,0,[1,7],[6]],
      [2782,1,[2],[]], [2278,1,[2],[3]], [765,2,[3],[]], [255,2,[3],[4]],
      [1831,2,[3],[7]], [510,3,[4],[5]], [2288,3,[4],[7]], [1121,5,[4],[2]],
      [115,5,[4],[3]], [951,6,[5],[4]], [1088,6,[5,7],[1]], [1831,6,[5,7],[2]],
    ],
  },
  {
    bits: "00001101", noOutside: [6], withOutside: [0],
    rows: [
      [3,0,[1],[]], [22,0,[1],[2]], [34,0,[1,7],[3]], [10,0,[1,7],[5]],
      [24,1,[2],[]], [47,1,[2],[3]], [33,2,[3],[]], [7,3,[4],[5]],
      [27,3,[4],[7]], [2,5,[4],[3]], [17,6,[5],[4]], [1,6,[5,7],[0]], [19,6,[5,7],[2]],
    ],
  },
  { bits: "00001101", noOutside: [], withOutside: [0, 6], rows: cuts["00001101"] },
  {
    bits: "00011101", noOutside: [0, 6], withOutside: [],
    rows: [
      [2,0,[1],[2]], [1,0,[1,7],[5]], [1,1,[2],[]], [1,5,[4],[]],
      [2,6,[5],[4]], [1,6,[5,7],[1]],
    ],
  },
  {
    bits: "00011101", noOutside: [0], withOutside: [6],
    rows: [
      [4,0,[1],[]], [44,0,[1],[2]], [5,0,[1,7],[4]], [46,0,[1,7],[5]],
      [1,0,[1,7],[6]], [23,1,[2],[]], [32,1,[2],[3]], [18,2,[3],[7]],
      [5,4,[3],[7]], [37,5,[4],[]], [8,5,[4],[2]], [6,5,[4],[3]],
      [9,6,[5],[]], [80,6,[5],[4]], [29,6,[5,7],[1]], [18,6,[5,7],[2]],
    ],
  },
  {
    bits: "00011101", noOutside: [6], withOutside: [0],
    rows: [
      [9,0,[1],[]], [80,0,[1],[2]], [18,0,[1,7],[4]], [29,0,[1,7],[5]],
      [37,1,[2],[]], [6,1,[2],[3]], [8,1,[2],[4]], [5,2,[3],[7]],
      [18,4,[3],[7]], [23,5,[4],[]], [32,5,[4],[3]], [4,6,[5],[]],
      [44,6,[5],[4]], [1,6,[5,7],[0]], [46,6,[5,7],[1]], [5,6,[5,7],[2]],
    ],
  },
  { bits: "00011101", noOutside: [], withOutside: [0, 6], rows: cuts["00011101"] },
];

function nearRoot(levels, root) {
  return levels[root] === 0 &&
    levels.every((level, j) => {
      const arc = ringDistance(root, j);
      return level >= Math.min(arc, 6 - arc);
    });
}

function checkDegreeCase({ bits, noOutside, withOutside, rows }) {
  const moves = rows.map(row => certifiedMove(bits, row));
  const saving = moves.reduce((sum, move) => sum + move.weight * move.saving, 0);
  if (saving <= 0) throw Error("No positive net saving");
  const permitted = all.filter(levels =>
    noOutside.every(i => levels[i] === 1 + Math.min(levels[(i + 7) % 8], levels[(i + 1) % 8])));
  const weighted = levels => moves.reduce((sum, move) => sum + move.weight * impact(move, levels), 0);
  const maxOutside = Math.max(...permitted.map(weighted));
  let onCycle = 0;
  for (let j = 0; j < 8; j++)
    onCycle += weighted(Array.from({ length: 8 }, (_, i) => ringDistance(i, j)));

  let unavoidableLoss = 0;
  for (const root of withOutside) {
    const nearby = permitted.filter(levels => nearRoot(levels, root));
    const best = Math.max(...nearby.map(weighted));
    if (!Number.isFinite(best)) throw Error("No allowed nearby type");
    unavoidableLoss += maxOutside - best;
  }

  // The off-cycle neighbours counted at different roots are distinct: sharing
  // one would give a cycle of length at most six, below the required eight.
  const slope = maxOutside - saving;
  const threshold = 8 * maxOutside - onCycle + unavoidableLoss;
  if (threshold < 0) throw Error("The certificate must give a nonnegative threshold");
  const minimumOrder = slope <= 0 ? null : Math.floor(threshold / slope) + 1;
  return { bits, noOutside, withOutside, slope, threshold, minimumOrder };
}

const cases = degreeCuts.map(checkDegreeCase);
if (JSON.stringify(cases.map(c => c.minimumOrder)) !== "[null,201,229,null,303,303,157]")
  throw Error("Unexpected degree-sensitive octagon cutoffs");
for (const checked of cases) console.log(checked);
