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

const directedBounds = [
  [9, 41, [[2, 4], [3, 5]]],
  [10, 45, [[2, 5], [3, 5]]],
  [11, 56, [[3, 9]]],
  [12, 59, [[2, 9], [4, 4]]],
  [13, 71, [[2, 6], [3, 7]]],
  [14, 73, [[2, 11], [4, 4]]],
  [15, 87, [[2, 13], [4, 4]]],
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

function leastMask(mask) {
  let best = mask;
  for (let shift = 0; shift < 8; shift++) {
    for (const reflected of [false, true]) {
      let rotated = 0;
      for (let edge = 0; edge < 8; edge++) {
        const source = reflected ? (shift - edge - 1 + 16) % 8 : (shift + edge) % 8;
        const direction = ((mask >> source) & 1) ^ Number(reflected);
        rotated |= direction << edge;
      }
      best = Math.min(best, rotated);
    }
  }
  return best;
}

function octagonMove(mask, buyer, purchases, multiplicity) {
  const left = (buyer + 7) % 8, right = (buyer + 1) % 8;
  const owned = [];
  if ((mask >> buyer) & 1) owned.push(right);
  if (!((mask >> left) & 1)) owned.push(left);
  const incoming = [left, right].filter(v => !owned.includes(v));
  require(purchases.length === new Set(purchases).size &&
    purchases.every(v => Number.isInteger(v) && v >= 0 && v < 8 &&
      v !== buyer && !incoming.includes(v)), "Invalid octagon purchase");
  require(Number.isInteger(multiplicity) && multiplicity > 0, "Invalid multiplier");
  const sold = owned.filter(v => !purchases.includes(v));
  const edges = Array.from({length: 8}, (_, i) => [(i + 1) % 8, (i + 7) % 8]);
  edges[buyer] = [...incoming, ...purchases];
  for (let v = 0; v < 8; v++) {
    if (v === buyer) continue;
    edges[v] = edges[v].filter(w => w !== buyer);
    if (edges[buyer].includes(v)) edges[v].push(buyer);
  }
  const after = Array(8).fill(-1), queue = [buyer];
  after[buyer] = 0;
  for (let i = 0; i < queue.length; i++) {
    const v = queue[i];
    for (const w of edges[v]) {
      if (after[w] >= 0) continue;
      after[w] = after[v] + 1;
      queue.push(w);
    }
  }
  require(queue.length === 8, "Disconnected deviation");
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

function verifyOctagons() {
  const reps = new Set();
  for (let mask = 0; mask < 256; mask++) reps.add(leastMask(mask));
  require(reps.size === 22 && reps.size === Object.keys(octagonWeights).length,
    "Incomplete octagon representatives");
  const groups = [...reps].map(mask => {
    const moves = octagonWeights[mask].map(([u, s, a]) => octagonMove(mask, u, s, a));
    const saved = moves.reduce((sum, m) => sum + m.multiplicity * m.saved, 0);
    require(saved > 0, "No saved purchase");
    return {moves, saved};
  });
  let labelCount = 0;
  visitLabels(8, false, labels => {
    labelCount++;
    for (const {moves, saved} of groups) {
      const increase = moves.reduce((sum, m) =>
        sum + m.multiplicity * distanceIncrease(labels, m), 0);
      require(5 * increase <= 7 * saved, "Octagon inequality fails");
    }
  });
  require(labelCount === 1107, "Wrong octagon label count");
  return {representatives: groups.length, labels: labelCount};
}

function verifyDirected(size, upper, swaps) {
  const choices = [[-1, 4], ...swaps];
  const distances = choices.map(([target]) => Array.from({length: size}, (_, k) => {
    if (!k) return 0;
    return target < 0 ? size - k : Math.min(size - k, 1 + Math.abs(target - k));
  }));
  let maximum = -Infinity, labelCount = 0;
  visitLabels(size, true, labels => {
    labelCount++;
    let value = 0;
    for (let u = 0; u < size; u++) {
      const old = labels[u];
      const unchanged = labels[(u + 1) % size] + 1 !== old;
      const best = choices.map(() => unchanged ? 0 : Infinity);
      for (let k = 1; k < size; k++) {
        const difference = labels[(u + k) % size] - old;
        if (difference >= Math.min(k, size - k)) continue;
        for (let j = 0; j < choices.length; j++) {
          best[j] = Math.min(best[j], distances[j][k] + difference);
        }
      }
      for (let j = 0; j < choices.length; j++) value += choices[j][1] * best[j];
    }
    maximum = Math.max(maximum, value);
  });
  require(maximum <= upper && 20 * upper <= 29 * 4 * size, "Directed-cycle inequality fails");
  return {size, representatives: labelCount, maximum, upper};
}

const verification = {
  octagon: verifyOctagons(),
  directed: directedBounds.map(row => verifyDirected(...row)),
};

console.log(JSON.stringify(verification, null, 2));
