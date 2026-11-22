const octagonWeights = {
  0: [[0,[],4],[0,[5],2],[1,[],2],[1,[5],1],[1,[6],2],[2,[],2],[2,[6],2],[2,[7],1],[3,[],4],[3,[7],1],[4,[],5],[4,[0],1],[5,[],2],[5,[1],2],[5,[2],3],[6,[],3],[6,[2],2],[7,[],2],[7,[3],5]],
  1: [[0,[2],1],[0,[3],1],[0,[4],1],[0,[5],1],[0,[6],1],[3,[],1],[4,[],1],[5,[],2],[5,[1],1],[6,[],2],[7,[],2]],
  3: [[0,[2],2],[0,[3],1],[0,[4],1],[0,[6],2],[1,[],1],[4,[],1],[5,[],2],[6,[],2],[7,[],2]],
  5: [[0,[3],1],[0,[4],1],[2,[7],1],[5,[],1],[7,[],1]],
  7: [[0,[3],2],[0,[4],1],[0,[6],1],[1,[],1],[2,[],1],[5,[],1],[6,[],1],[7,[],1]],
  9: [[0,[4],2],[3,[7],1],[5,[],1],[7,[],1]],
  11: [[0,[4],2],[3,[7],1],[5,[],1],[7,[],1]],
  13: [[0,[1],2],[0,[4],2],[0,[5],1],[0,[6],1],[2,[5],1],[2,[6],1],[2,[7],1],[3,[],1],[5,[],1],[5,[1],1],[6,[],2],[7,[],2]],
  15: [[0,[2],1],[0,[4],1],[0,[5],2],[1,[],1],[2,[],1],[3,[],1],[6,[],1],[7,[],1]],
  17: [[0,[1],1],[0,[3],1],[0,[4],1],[0,[5],5],[2,[],2],[3,[],1],[4,[1],7],[4,[7],1],[6,[],1]],
  19: [[0,[2],1],[0,[3],1],[0,[4],1],[0,[5],1],[0,[6],1],[1,[],1],[4,[1],1],[4,[7],2],[6,[],1],[7,[],1]],
  21: [[0,[3],1],[0,[4],1],[2,[7],1],[4,[1],1]],
  23: [[0,[2],1],[0,[3],1],[0,[4],1],[0,[5],1],[0,[6],1],[1,[],1],[2,[],1],[4,[1],1],[4,[7],1],[7,[],1]],
  25: [[0,[2],1],[0,[4],3],[0,[5],1],[0,[6],1],[3,[1],4],[3,[7],1],[6,[],1],[7,[],1]],
  27: [[0,[2],2],[0,[4],1],[0,[5],1],[0,[6],1],[1,[],1],[3,[1],1],[3,[7],1],[6,[],1],[7,[],1]],
  29: [[0,[1],2],[0,[3],2],[0,[4],1],[0,[5],1],[2,[1],3],[2,[5],3],[2,[6],1],[2,[7],1],[3,[],2],[4,[],1],[6,[],1],[7,[],2]],
  37: [[0,[4],1],[0,[6],1],[2,[6],2],[5,[1],2],[5,[3],1],[7,[],1]],
  43: [[0,[4],1],[0,[6],1],[3,[7],1],[5,[1],1],[5,[2],1]],
  45: [[0,[4],1],[0,[6],1],[2,[6],2],[5,[1],2],[5,[3],1],[7,[],1]],
  51: [[0,[2],1],[0,[3],1],[0,[4],1],[0,[5],2],[0,[6],1],[1,[],1],[3,[],1],[4,[1],2],[4,[2],2],[4,[7],2],[7,[],1]],
  53: [[0,[3],1],[0,[4],1],[2,[7],1],[4,[1],1]],
  85: [[0,[4],1],[2,[7],1],[4,[1],1],[6,[3],1]]
};

const certificates = [
  {size:8,num:7,den:5,labelCount:1107,orientationCount:22,witnesses:octagonWeights},
  {size:9,num:3,den:2,labelCount:3139,orientationCount:30,witnesses:{
    0: [[0,[],3],[0,[5],1],[0,[6],2],[1,[],4],[1,[6],1],[1,[7],2],[2,[],4],[2,[7],1],[2,[8],2],[3,[],3],[3,[0],4],[3,[8],1],[4,[],3],[4,[1],4],[5,[],3],[5,[1],2],[5,[2],2],[6,[],4],[6,[2],1],[6,[3],1],[7,[],3],[7,[3],2],[7,[4],2],[8,[],3],[8,[4],1],[8,[5],3]],
    1: [[0,[2],2],[0,[3],2],[0,[4],5],[0,[5],4],[0,[6],2],[3,[],1],[3,[8],1],[4,[],2],[4,[1],1],[5,[],4],[5,[1],1],[6,[],6],[6,[1],1],[7,[],5],[8,[],4]],
    3: [[0,[2],3],[0,[3],1],[0,[4],3],[0,[5],4],[0,[6],6],[1,[],2],[3,[],1],[4,[],1],[4,[1],1],[5,[],4],[5,[1],1],[6,[],4],[6,[1],2],[6,[2],1],[7,[],7],[8,[],4]],
    5: [[0,[1],1],[0,[3],5],[0,[4],2],[0,[5],2],[0,[7],1],[2,[1],1],[2,[5],1],[2,[6],2],[2,[7],1],[2,[8],1],[4,[],1],[5,[],2],[5,[1],1],[6,[],3],[6,[1],2],[7,[],4],[8,[],4]],
    7: [[0,[3],5],[0,[4],1],[0,[5],4],[0,[6],4],[0,[7],1],[1,[],2],[2,[],2],[4,[],1],[5,[],1],[5,[1],2],[6,[],4],[6,[2],1],[7,[],5],[8,[],4]],
    9: [[0,[2],1],[0,[4],1],[3,[1],1],[3,[8],1]],
    11: [[0,[2],1],[0,[4],1],[3,[1],1],[3,[8],1]],
    13: [[0,[1],2],[0,[3],1],[0,[4],5],[0,[5],2],[0,[7],1],[2,[1],2],[2,[6],3],[2,[8],2],[3,[],2],[5,[],1],[6,[],2],[6,[1],1],[7,[],3],[8,[],4]],
    15: [[0,[2],1],[0,[3],4],[0,[4],4],[0,[5],3],[0,[6],3],[0,[7],1],[1,[],4],[2,[],3],[3,[],2],[3,[8],1],[5,[],1],[6,[],3],[6,[2],1],[7,[],4],[8,[],4]],
    17: [[0,[4],1],[4,[8],1]],
    19: [[0,[4],1],[4,[8],1]],
    21: [[0,[4],1],[4,[8],1]],
    23: [[0,[4],1],[4,[8],1]],
    25: [[0,[2],1],[0,[4],1],[3,[1],1],[3,[8],1]],
    27: [[0,[2],1],[0,[4],1],[3,[1],1],[3,[8],1]],
    29: [[0,[1],4],[0,[3],5],[0,[4],3],[0,[5],3],[0,[6],1],[0,[7],1],[2,[1],3],[2,[5],2],[2,[7],3],[2,[8],6],[3,[],3],[4,[],1],[6,[],2],[6,[1],2],[7,[],3],[8,[],5]],
    35: [[0,[4],1],[0,[6],1],[5,[1],1],[5,[8],1]],
    37: [[0,[4],1],[2,[6],1],[5,[1],1],[5,[8],1]],
    39: [[0,[4],1],[0,[6],1],[5,[1],1],[5,[8],1]],
    41: [[0,[4],1],[3,[6],1],[5,[2],1],[5,[8],1]],
    43: [[0,[4],1],[3,[6],1],[5,[2],1],[5,[8],1]],
    45: [[0,[4],1],[2,[6],1],[5,[1],1],[5,[8],1]],
    51: [[0,[4],1],[4,[8],1]],
    53: [[0,[4],1],[4,[8],1]],
    57: [[0,[2],1],[0,[4],1],[3,[1],1],[3,[8],1]],
    73: [[0,[4],1],[3,[7],1],[3,[8],1],[6,[2],1]],
    75: [[0,[4],1],[3,[7],1],[3,[8],1],[6,[2],1]],
    77: [[0,[4],1],[2,[5],1],[2,[7],1],[3,[],1],[6,[1],1],[6,[3],1]],
    83: [[0,[4],1],[4,[8],1]],
    85: [[0,[4],1],[4,[8],1]]
  }},
  {size:10,num:3,den:2,labelCount:8953,orientationCount:62,witnesses:{
    0: [[0,[],3],[0,[5],1],[0,[6],3],[0,[7],1],[1,[],5],[1,[6],1],[1,[7],2],[2,[],5],[2,[8],3],[2,[9],2],[3,[],6],[3,[0],2],[3,[9],1],[4,[],4],[4,[0],3],[4,[1],3],[4,[9],2],[5,[],4],[5,[0],1],[5,[1],5],[5,[2],2],[5,[3],1],[6,[],5],[6,[2],4],[6,[3],2],[7,[],5],[7,[2],1],[7,[3],2],[7,[4],3],[8,[],3],[8,[3],2],[8,[4],4],[8,[5],2],[9,[],2],[9,[5],6],[9,[6],1]],
    1: [[0,[2],2],[0,[3],1],[0,[4],4],[0,[5],4],[0,[6],6],[0,[7],2],[2,[8],2],[3,[],1],[3,[9],1],[4,[],1],[4,[9],3],[5,[],2],[5,[1],4],[6,[],2],[6,[1],6],[7,[],6],[8,[],5],[9,[],4]],
    3: [[0,[2],2],[0,[3],3],[0,[4],2],[0,[5],5],[0,[6],5],[0,[7],5],[1,[],3],[3,[],1],[3,[9],2],[4,[],1],[4,[9],4],[5,[],2],[5,[1],2],[6,[],2],[6,[1],2],[6,[2],6],[7,[],4],[7,[1],1],[7,[2],4],[8,[],5],[9,[],4]],
    5: [[0,[1],1],[0,[3],5],[0,[4],3],[0,[5],3],[0,[6],1],[0,[7],1],[2,[1],1],[2,[6],3],[2,[7],4],[2,[8],2],[2,[9],2],[4,[],1],[5,[],1],[5,[1],2],[6,[],2],[6,[1],3],[7,[],3],[7,[1],2],[7,[3],1],[8,[],6],[8,[3],1],[9,[],5]],
    7: [[0,[2],1],[0,[3],4],[0,[4],1],[0,[5],4],[0,[6],6],[0,[7],7],[1,[],3],[2,[],2],[2,[7],1],[4,[],1],[4,[9],3],[5,[],1],[5,[1],2],[5,[9],1],[6,[],3],[6,[1],5],[6,[2],2],[7,[],4],[7,[3],5],[8,[],5],[8,[3],3],[9,[],5]],
    9: [[0,[2],3],[0,[3],1],[0,[4],8],[0,[5],1],[0,[6],2],[0,[7],1],[2,[],1],[3,[1],5],[3,[7],2],[3,[8],1],[3,[9],5],[5,[],1],[6,[],1],[6,[1],1],[7,[],2],[7,[1],1],[8,[],3],[9,[],3],[9,[4],2]],
    11: [[0,[2],6],[0,[3],1],[0,[4],8],[0,[5],1],[0,[7],2],[1,[],1],[3,[1],3],[3,[7],3],[3,[8],1],[3,[9],8],[5,[],1],[6,[],1],[7,[],1],[7,[2],3],[8,[],3],[9,[],4],[9,[4],1]],
    13: [[0,[1],2],[0,[3],1],[0,[4],7],[0,[5],3],[0,[6],1],[0,[7],1],[2,[1],1],[2,[6],1],[2,[7],5],[2,[8],2],[2,[9],3],[3,[],2],[5,[],1],[5,[1],2],[6,[],2],[6,[1],2],[7,[],2],[7,[1],3],[8,[],5],[8,[4],1],[9,[],5],[9,[4],1]],
    15: [[0,[3],3],[0,[4],6],[0,[5],3],[0,[6],3],[0,[7],8],[1,[],3],[1,[4],2],[1,[5],1],[2,[],4],[2,[8],1],[3,[],2],[3,[8],5],[5,[],1],[5,[1],1],[6,[],1],[6,[1],5],[6,[2],1],[7,[],4],[7,[2],1],[7,[3],2],[8,[],6],[8,[4],1],[9,[],5],[9,[4],4]],
    17: [[0,[3],1],[0,[5],1],[4,[1],1],[4,[9],1]],
    19: [[0,[3],1],[0,[5],1],[4,[1],1],[4,[9],1]],
    21: [[0,[3],1],[0,[5],1],[4,[1],1],[4,[9],1]],
    23: [[0,[3],1],[0,[5],1],[4,[1],1],[4,[9],1]],
    25: [[0,[2],4],[0,[3],1],[0,[4],7],[0,[5],3],[0,[6],1],[2,[],1],[3,[1],7],[3,[6],1],[3,[7],2],[3,[9],6],[4,[],2],[6,[],1],[7,[],1],[8,[],2],[9,[],3],[9,[4],1]],
    27: [[0,[2],6],[0,[4],6],[0,[5],2],[0,[6],1],[0,[7],1],[1,[],1],[3,[1],3],[3,[6],1],[3,[7],1],[3,[8],1],[3,[9],7],[4,[],2],[6,[],1],[7,[],2],[8,[],2],[9,[],3]],
    29: [[0,[1],3],[0,[3],3],[0,[4],3],[0,[5],6],[0,[6],2],[2,[1],1],[2,[5],1],[2,[6],1],[2,[7],3],[2,[8],3],[2,[9],6],[3,[],3],[3,[8],1],[4,[],2],[6,[],2],[6,[1],4],[7,[],2],[7,[1],2],[8,[],5],[8,[5],1],[9,[],5],[9,[5],3]],
    31: [[0,[2],1],[0,[3],3],[0,[4],3],[0,[5],7],[0,[6],4],[0,[7],3],[1,[],4],[1,[5],1],[2,[],4],[2,[5],1],[2,[6],1],[3,[],3],[3,[8],1],[4,[],1],[4,[8],1],[4,[9],3],[6,[],1],[6,[1],2],[6,[2],2],[7,[],3],[7,[3],1],[8,[],5],[9,[],4]],
    33: [[0,[5],1],[5,[1],1]],
    35: [[0,[5],1],[5,[1],1]],
    37: [[0,[5],1],[5,[1],1]],
    39: [[0,[5],1],[5,[1],1]],
    41: [[0,[5],1],[5,[1],1]],
    43: [[0,[5],1],[5,[1],1]],
    45: [[0,[5],1],[5,[1],1]],
    47: [[0,[5],1],[5,[1],1]],
    49: [[0,[3],1],[0,[5],1],[4,[1],1],[4,[9],1]],
    51: [[0,[3],1],[0,[5],1],[4,[1],1],[4,[9],1]],
    53: [[0,[3],1],[0,[5],1],[4,[1],1],[4,[9],1]],
    55: [[0,[3],1],[0,[5],1],[4,[1],1],[4,[9],1]],
    57: [[0,[2],6],[0,[4],6],[0,[5],1],[0,[6],2],[2,[],1],[3,[1],5],[3,[6],2],[3,[7],1],[3,[8],2],[3,[9],7],[4,[],2],[5,[],2],[7,[],1],[8,[],1],[9,[],3]],
    59: [[0,[2],7],[0,[4],5],[0,[5],1],[0,[6],1],[0,[7],1],[1,[],1],[3,[1],3],[3,[6],1],[3,[8],3],[3,[9],7],[4,[],2],[5,[],1],[7,[],1],[8,[],1],[9,[],3]],
    61: [[0,[1],3],[0,[1,6],9],[0,[3],24],[0,[4],6],[0,[5],9],[0,[6],38],[2,[1],3],[2,[1,6],11],[2,[5],1],[2,[6],33],[2,[7],7],[2,[8],10],[2,[9],22],[3,[],25],[3,[6],7],[4,[],3],[4,[8],1],[5,[],1],[5,[1],43],[7,[],1],[7,[1],39],[8,[],3],[8,[4],1],[8,[6],1],[9,[],24],[9,[6],8]],
    69: [[0,[5],1],[2,[7],1],[6,[1],1],[6,[9],1]],
    71: [[0,[5],1],[0,[7],1],[6,[1],1],[6,[9],1]],
    73: [[0,[5],1],[0,[7],1],[3,[8],1],[6,[1],1],[6,[2],1]],
    75: [[0,[5],1],[0,[7],1],[3,[8],1],[6,[1],1],[6,[2],1]],
    77: [[0,[5],1],[2,[7],1],[6,[1],1],[6,[9],1]],
    83: [[0,[5],1],[0,[7],1],[4,[9],1],[6,[1],1]],
    85: [[0,[5],1],[2,[5],1],[2,[7],1],[4,[1],1],[4,[9],1],[6,[1],1],[6,[3],1]],
    87: [[0,[5],1],[0,[7],1],[4,[9],1],[6,[1],1]],
    89: [[0,[5],1],[0,[7],1],[3,[8],1],[6,[1],1],[6,[2],1]],
    91: [[0,[5],1],[0,[7],1],[3,[8],1],[6,[1],1],[6,[2],1]],
    93: [[0,[5],1],[2,[7],1],[6,[1],1],[6,[9],1]],
    99: [[0,[5],1],[5,[1],1]],
    101: [[0,[5],1],[5,[1],1]],
    103: [[0,[5],1],[5,[1],1]],
    105: [[0,[5],1],[5,[1],1]],
    107: [[0,[5],1],[5,[1],1]],
    109: [[0,[5],1],[5,[1],1]],
    115: [[0,[3],1],[0,[5],1],[4,[1],1],[4,[9],1]],
    117: [[0,[3],1],[0,[5],1],[4,[1],1],[4,[9],1]],
    147: [[0,[3],1],[0,[5],1],[4,[8],1],[4,[9],1],[7,[2],1]],
    149: [[0,[3],1],[0,[5],1],[2,[6],1],[2,[8],1],[4,[1],1],[4,[9],1],[7,[1],1],[7,[2],1]],
    155: [[0,[2],2],[0,[4],1],[0,[5],1],[0,[6],1],[0,[8],1],[1,[],1],[3,[1],1],[3,[5],1],[3,[8],3],[3,[9],1],[4,[],1],[6,[],1],[7,[1],1],[7,[2],2],[7,[4],1],[7,[5],1],[7,[9],1],[9,[],1]],
    165: [[0,[5],1],[5,[1],1]],
    171: [[0,[5],1],[5,[1],1]],
    173: [[0,[5],1],[5,[1],1]],
    179: [[0,[3],1],[0,[5],1],[4,[8],1],[4,[9],1],[7,[2],1]],
    181: [[0,[3],1],[0,[5],1],[2,[6],1],[2,[8],1],[4,[1],1],[4,[9],1],[7,[1],1],[7,[2],1]],
    205: [[0,[5],1],[2,[7],1],[6,[1],1],[6,[9],1]],
    213: [[0,[5],1],[2,[5],1],[2,[7],1],[4,[1],1],[4,[9],1],[6,[1],1],[6,[3],1]],
    341: [[0,[5],1],[2,[7],1],[4,[9],1],[6,[1],1],[8,[3],1]]
  }}
];

function require(condition, message) {
  if (!condition) throw new Error(message);
}

function cycleDistance(size, a, b) {
  const length = Math.abs(a - b);
  return Math.min(length, size - length);
}

function visitLabels(size, rotations, visit) {
  const maximum = Math.floor(size / 2);
  const word = Array(size).fill(0);
  function firstInOrbit() {
    for (let shift = 1; shift < size; shift++) {
      if (word[shift] !== 0) continue;
      for (let j = 1; j < size; j++) {
        const comparison = word[(j + shift) % size] - word[j];
        if (comparison < 0) return false;
        if (comparison > 0) break;
      }
    }
    return true;
  }
  function extend(index, hasZero) {
    if (index === size) {
      if (hasZero && Math.abs(word[0] - word[size - 1]) <= 1 &&
          (!rotations || firstInOrbit())) visit(word);
      return;
    }
    const lower = index ? Math.max(0, word[index - 1] - 1) : 0;
    const upper = index ? Math.min(maximum, word[index - 1] + 1) : maximum;
    for (let value = lower; value <= upper; value++) {
      word[index] = value;
      extend(index + 1, hasZero || value === 0);
    }
  }
  if (rotations) extend(1, true);
  else extend(0, false);
}


function leastMask(size, mask) {
  let minimum = mask;
  for (let shift = 0; shift < size; shift++) {
    for (const reflected of [false, true]) {
      let transformed = 0;
      for (let edge = 0; edge < size; edge++) {
        const source = reflected
          ? (shift - edge - 1 + 2 * size) % size
          : (shift + edge) % size;
        const digit = ((mask >> source) & 1) ^ Number(reflected);
        transformed |= digit << edge;
      }
      minimum = Math.min(minimum, transformed);
    }
  }
  return minimum;
}

function cycleMove(size, mask, buyer, purchases, multiplicity) {
  const left = (buyer + size - 1) % size;
  const right = (buyer + 1) % size;
  const owned = [];
  if ((mask >> buyer) & 1) owned.push(right);
  if (!((mask >> left) & 1)) owned.push(left);
  const incoming = [left, right].filter(v => !owned.includes(v));
  require(purchases.length === new Set(purchases).size &&
    purchases.every(v => Number.isInteger(v) && v >= 0 && v < size &&
      v !== buyer && !incoming.includes(v)), "Invalid cycle purchase");
  require(Number.isInteger(multiplicity) && multiplicity > 0, "Invalid multiplier");
  const sold = owned.filter(v => !purchases.includes(v));
  const edges = Array.from({length: size}, (_, i) => [(i + 1) % size, (i + size - 1) % size]);
  edges[buyer] = [...incoming, ...purchases];
  for (let v = 0; v < size; v++) {
    if (v === buyer) continue;
    edges[v] = edges[v].filter(w => w !== buyer);
    if (edges[buyer].includes(v)) edges[v].push(buyer);
  }
  const after = Array(size).fill(-1), queue = [buyer];
  after[buyer] = 0;
  for (let i = 0; i < queue.length; i++) {
    const v = queue[i];
    for (const w of edges[v]) {
      if (after[w] >= 0) continue;
      after[w] = after[v] + 1;
      queue.push(w);
    }
  }
  require(queue.length === size, "Disconnected deviation");
  return {buyer, sold, after, multiplicity, saved: owned.length - purchases.length};
}

function distanceIncrease(labels, move) {
  const {buyer, sold, after} = move;
  const old = labels[buyer];
  let result = sold.every(v => labels[v] + 1 !== old) ? 0 : Infinity;
  for (let v = 0; v < labels.length; v++) {
    if (labels[v] >= cycleDistance(labels.length, buyer, v) + old) continue;
    result = Math.min(result, after[v] + labels[v] - old);
  }
  require(Number.isFinite(result), "No retained route");
  return result;
}

function verifyArbitrary(certificate) {
  const {size, num, den, witnesses, labelCount, orientationCount} = certificate;
  const reps = new Set();
  for (let mask = 0; mask < 1 << size; mask++) reps.add(leastMask(size, mask));
  require(reps.size === orientationCount && reps.size === Object.keys(witnesses).length,
    "Incomplete orientation coverage");
  const groups = [...reps].map(mask => {
    const moves = witnesses[mask].map(([u, s, a]) => cycleMove(size, mask, u, s, a));
    const saved = moves.reduce((sum, m) => sum + m.multiplicity * m.saved, 0);
    require(saved > 0, "No saved purchase");
    return {moves, saved};
  });
  let checked = 0;
  visitLabels(size, false, labels => {
    checked++;
    for (const {moves, saved} of groups) {
      const increase = moves.reduce((sum, m) =>
        sum + m.multiplicity * distanceIncrease(labels, m), 0);
      require(den * increase <= num * saved, "Unrestricted cycle inequality fails");
    }
  });
  require(checked === labelCount, "Wrong label count");
  return {size, labels: checked, orientations: groups.length, num, den};
}

const directedBounds = [
  [11,56,[[3,9]]],
  [12,59,[[2,9],[4,4]]],
  [13,71,[[2,6],[3,7]]],
  [14,73,[[2,11],[4,4]]],
  [15,87,[[2,13],[4,4]]],
  [16,92,[[2,9],[5,6]]],
  [17,100,[[2,10],[5,6]]],
  [18,111,[[2,14],[4,5]]],
  [19,123,[[3,9],[6,4]]]
];


function forDirectedLabels(size, visit) {
  const word = new Int8Array(2 * size);
  const half = Math.floor(size / 2);
  function canonical() {
    for (let shift = 1; shift < size; shift++) {
      if (word[shift] !== 0) continue;
      for (let j = 1; j < size; j++) {
        if (word[shift + j] === word[j]) continue;
        if (word[shift + j] < word[j]) return false;
        break;
      }
    }
    return true;
  }
  function extend(i) {
    if (i === size) {
      if (canonical()) visit(word);
      return;
    }
    const lower = Math.max(0, word[i - 1] - 1);
    const upper = Math.min(half, word[i - 1] + 1, size - i);
    for (let x = lower; x <= upper; x++) {
      word[i] = word[i + size] = x;
      extend(i + 1);
    }
  }
  extend(1);
}

function directedImpactRow(size, word, targets, arc, row) {
  row.fill(0);
  for (let u = 0; u < size; u++) {
    const old = word[u];
    let deletion = 0;
    if (word[u + 1] + 1 === old) {
      for (let k = size - 1; k >= 1; k--) {
        const difference = word[u + k] - old;
        if (difference < arc[k]) {
          deletion = size - k + difference;
          break;
        }
      }
    }
    row[0] += deletion;
    for (let j = 0; j < targets.length; j++) {
      const target = targets[j];
      let value = deletion;
      const atTarget = word[u + target] - old;
      if (atTarget < arc[target]) {
        value = Math.min(value, 1 + atTarget);
      } else {
        for (let k = target - 1; k >= 1; k--) {
          const difference = word[u + k] - old;
          if (difference < arc[k]) {
            value = Math.min(value, 1 + target - k + difference);
            break;
          }
        }
        for (let k = target + 1; k < size; k++) {
          const difference = word[u + k] - old;
          if (difference < arc[k]) {
            value = Math.min(value, 1 + k - target + difference);
            break;
          }
        }
      }
      row[j + 1] += value;
    }
  }
}

function directReference(size, word, targets, arc, reference) {
  reference.fill(0);
  const operations = [-1, ...targets];
  for (let u = 0; u < size; u++) {
    for (let j = 0; j < operations.length; j++) {
      const target = operations[j];
      const old = word[u];
      let value = word[u + 1] + 1 !== old ? 0 : Infinity;
      for (let k = 1; k < size; k++) {
        const difference = word[u + k] - old;
        if (difference >= arc[k]) continue;
        const walk = target < 0 ? size - k : Math.min(size - k, 1 + Math.abs(target - k));
        value = Math.min(value, walk + difference);
      }
      reference[j] += value;
    }
  }
}

function verifyDirected(size, upper, swaps) {
  const targets = swaps.map(([t]) => t);
  const arc = Array.from({length: size}, (_, k) => Math.min(k, size - k));
  const row = new Int16Array(targets.length + 1), reference = new Int16Array(row.length);
  let maximum = -Infinity, count = 0;
  forDirectedLabels(size, word => {
    count++;
    directedImpactRow(size, word, targets, arc, row);
    if (size <= 15 || count % 1024 === 1) {
      directReference(size, word, targets, arc, reference);
      require(row.every((v, j) => v === reference[j]), "Route formula disagrees with direct check");
    }
    let value = 4 * row[0];
    for (let j = 0; j < swaps.length; j++) value += swaps[j][1] * row[j + 1];
    maximum = Math.max(maximum, value);
  });
  require(maximum <= upper, "Directed-cycle inequality fails");
  require(76 * upper <= 123 * 4 * size, "Largest claimed ratio is too small");
  require(size > 17 || upper <= 6 * size, "Shorter claimed ratio is too small");
  return {size, labelOrbits: count, maximum, upper};
}

console.log(JSON.stringify({
  unrestricted: certificates.map(verifyArbitrary),
  directed: directedBounds.map(row => verifyDirected(...row)),
}, null, 2));
