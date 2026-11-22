// A necessary number of outside vertices attached to the path interior.
function chainExcess(length, startDegree, endDegree, twoLayers) {
  if (length < 2) return 0;

  let lowerBound = Infinity;
  const purchase = Array(length);
  function checkOrientation() {
    const weights = Array(length + 1).fill(1);
    // A swap across the skipped vertex improves the next one to three
    // destinations. Within two steps of an end, it also improves all
    // other neighbours of the end. When the end is the actual new endpoint,
    // each other branch also supplies a distinct second-layer vertex.
    for (let i = 1; i < length; i++) {
      if (purchase[i]) continue;
      let improved = i <= 2 ? startDegree - 1 : 0;
      if (twoLayers && i === 1) improved += startDegree - 1;
      for (let j = Math.max(0, i - 3); j < i; j++) improved += weights[j];
      weights[i] = Math.max(weights[i], improved);
    }
    for (let i = length - 1; i > 0; i--) {
      if (!purchase[i - 1]) continue;
      let improved = length - i <= 2 ? endDegree - 1 : 0;
      if (twoLayers && length - i === 1) improved += endDegree - 1;
      for (let j = i + 1; j <= Math.min(length, i + 3); j++) improved += weights[j];
      weights[i] = Math.max(weights[i], improved);
    }
    lowerBound = Math.min(lowerBound, weights.reduce((sum, value) => sum + value - 1, 0));
  }

  // A forward purchase followed by a backward one is forbidden at
  // separation two or three, hence at every separation of at least two.
  // The only possible inversion is a single adjacent pair.
  for (let boundary = 0; boundary <= length; boundary++) {
    purchase.fill(0, 0, boundary);
    purchase.fill(1, boundary);
    checkOrientation();
    if (boundary > 0 && boundary < length) {
      purchase[boundary - 1] = 1;
      purchase[boundary] = 0;
      checkOrientation();
    }
  }
  return lowerBound;
}

const bounds = [];
const twoLayerBounds = [];

export function chainAttachmentExcess(length, startDegree, endDegree, twoLayers = false) {
  const cache = twoLayers ? twoLayerBounds : bounds;
  const smaller = Math.min(startDegree, endDegree);
  const larger = Math.max(startDegree, endDegree);
  const byLength = cache[length] ??= [];
  const bySmallerDegree = byLength[smaller] ??= [];
  return bySmallerDegree[larger] ??= chainExcess(length, smaller, larger, twoLayers);
}
