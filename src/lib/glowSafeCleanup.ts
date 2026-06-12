export type GlowFringeMode = 'reduce' | 'remove';

export type RGB = [number, number, number];

export interface GlowSafeOptions {
  /** alpha <= dropAlpha 的像素直接设为全透明 */
  dropAlpha: number;

  /** 只有 alpha <= fringeAlphaMax 的边缘像素才会被视为白边/杂边候选 */
  fringeAlphaMax: number;

  /** 中性白检测亮度阈值，推荐 235~245 */
  whiteMin: number;

  /** 中性白检测饱和度上限，等于 max(r,g,b)-min(r,g,b)，推荐 18~35 */
  satMax: number;

  /** 目标杂边颜色，例如白色 [255,255,255]，也可以用吸管取样 */
  fringeColor: RGB;

  /** 与目标杂边颜色的 RGB 欧氏距离容差，推荐 24~48 */
  fringeColorTolerance: number;

  /** 只处理透明边缘附近的像素，推荐 1~2 */
  edgeRadius: number;

  /** reduce：保守降低透明度；remove：直接删除 */
  fringeMode: GlowFringeMode;

  /** reduce 模式下 alpha 乘数，推荐 0.45~0.7 */
  reduceFactor: number;

  /** 透明边 RGB 扩边次数，推荐 3~6 */
  bleedIterations: number;

  /** 是否删除孤立小点，默认 false。开强力清理时可设 true */
  removeIsolated: boolean;

  /** removeIsolated=true 时，少于该邻居数的像素会被删除，推荐 1 或 2 */
  isolatedMinNeighbors: number;

  /** 清理的目标颜色模式 */
  targetMode?: 'both' | 'target' | 'white';
}

export const DEFAULT_GLOW_SAFE_OPTIONS: GlowSafeOptions = {
  dropAlpha: 6,
  fringeAlphaMax: 64,
  whiteMin: 238,
  satMax: 28,
  fringeColor: [255, 255, 255],
  fringeColorTolerance: 36,
  edgeRadius: 2,
  fringeMode: 'reduce',
  reduceFactor: 0.55,
  bleedIterations: 4,
  removeIsolated: false,
  isolatedMinNeighbors: 1,
  targetMode: 'both',
};

const clampByte = (value: number): number => {
  if (!Number.isFinite(value)) return 0;
  if (value <= 0) return 0;
  if (value >= 255) return 255;
  return Math.round(value);
};

const clampInt = (value: number, min: number, max: number): number => {
  if (!Number.isFinite(value)) return min;
  return Math.max(min, Math.min(max, Math.round(value)));
};

const colorDistance = (r: number, g: number, b: number, target: RGB): number => {
  const dr = r - target[0];
  const dg = g - target[1];
  const db = b - target[2];
  return Math.sqrt(dr * dr + dg * dg + db * db);
};

const isNeutralWhiteLike = (
  r: number,
  g: number,
  b: number,
  whiteMin: number,
  satMax: number,
): boolean => {
  const maxC = Math.max(r, g, b);
  const minC = Math.min(r, g, b);
  const brightness = (r + g + b) / 3;
  const saturation = maxC - minC;
  return brightness >= whiteMin && saturation <= satMax;
};

const hasTransparentNeighbor = (
  data: Uint8ClampedArray,
  width: number,
  height: number,
  x: number,
  y: number,
  radius: number,
): boolean => {
  for (let dy = -radius; dy <= radius; dy++) {
    for (let dx = -radius; dx <= radius; dx++) {
      if (dx === 0 && dy === 0) continue;

      const nx = x + dx;
      const ny = y + dy;

      // 图像外部按透明处理。这样边缘一圈也会被识别为边缘区域。
      if (nx < 0 || nx >= width || ny < 0 || ny >= height) {
        return true;
      }

      const ni = (ny * width + nx) * 4;
      if (data[ni + 3] === 0) {
        return true;
      }
    }
  }
  return false;
};

const countVisibleNeighbors = (
  data: Uint8ClampedArray,
  width: number,
  height: number,
  x: number,
  y: number,
): number => {
  let count = 0;
  for (let dy = -1; dy <= 1; dy++) {
    for (let dx = -1; dx <= 1; dx++) {
      if (dx === 0 && dy === 0) continue;
      const nx = x + dx;
      const ny = y + dy;
      if (nx < 0 || nx >= width || ny < 0 || ny >= height) continue;
      const ni = (ny * width + nx) * 4;
      if (data[ni + 3] > 0) count++;
    }
  }
  return count;
};

/**
 * 对 alpha=0 的透明像素做 RGB 扩边。
 * 注意：只填 RGB，alpha 必须保持 0。
 * 目的：避免游戏引擎双线性采样 / 图集采样时读到透明区脏 RGB。
 */
export const bleedTransparentRGB = (
  input: Uint8ClampedArray,
  width: number,
  height: number,
  iterations: number,
): Uint8ClampedArray => {
  const totalPixels = width * height;
  let data = new Uint8ClampedArray(input);

  // colorSourceMask 表示该像素的 RGB 可以作为扩边来源。
  // 初始只有可见像素 alpha>0 是来源。
  let colorSourceMask = new Uint8Array(totalPixels);
  for (let p = 0; p < totalPixels; p++) {
    if (data[p * 4 + 3] > 0) colorSourceMask[p] = 1;
  }

  const safeIterations = clampInt(iterations, 0, 16);
  for (let iter = 0; iter < safeIterations; iter++) {
    const next = new Uint8ClampedArray(data);
    const nextMask = new Uint8Array(colorSourceMask);
    let changed = false;

    for (let y = 0; y < height; y++) {
      for (let x = 0; x < width; x++) {
        const p = y * width + x;
        const i = p * 4;

        // 只给完全透明并且还没有 RGB 来源的像素填色。
        if (data[i + 3] !== 0 || colorSourceMask[p] === 1) continue;

        let sumR = 0;
        let sumG = 0;
        let sumB = 0;
        let weightSum = 0;

        for (let dy = -1; dy <= 1; dy++) {
          for (let dx = -1; dx <= 1; dx++) {
            if (dx === 0 && dy === 0) continue;
            const nx = x + dx;
            const ny = y + dy;
            if (nx < 0 || nx >= width || ny < 0 || ny >= height) continue;

            const np = ny * width + nx;
            if (colorSourceMask[np] !== 1) continue;

            const ni = np * 4;
            // 可见像素按 alpha 加权；已经扩过的透明像素给较低权重。
            const sourceAlpha = data[ni + 3];
            const weight = sourceAlpha > 0 ? Math.max(1, sourceAlpha) : 32;

            sumR += data[ni] * weight;
            sumG += data[ni + 1] * weight;
            sumB += data[ni + 2] * weight;
            weightSum += weight;
          }
        }

        if (weightSum > 0) {
          next[i] = clampByte(sumR / weightSum);
          next[i + 1] = clampByte(sumG / weightSum);
          next[i + 2] = clampByte(sumB / weightSum);
          next[i + 3] = 0; // 关键：扩边只改 RGB，不能改 alpha。
          nextMask[p] = 1;
          changed = true;
        }
      }
    }

    data = next;
    colorSourceMask = nextMask;
    if (!changed) break;
  }

  return data;
};

export const runGlowSafeCleanup = (
  imageData: ImageData,
  partialOptions: Partial<GlowSafeOptions> = {},
  protectMask?: Uint8Array,
): ImageData => {
  const options: GlowSafeOptions = {
    ...DEFAULT_GLOW_SAFE_OPTIONS,
    ...partialOptions,
  };

  const width = imageData.width;
  const height = imageData.height;
  const totalPixels = width * height;

  const dropAlpha = clampInt(options.dropAlpha, 0, 64);
  const fringeAlphaMax = clampInt(options.fringeAlphaMax, dropAlpha, 255);
  const whiteMin = clampInt(options.whiteMin, 0, 255);
  const satMax = clampInt(options.satMax, 0, 255);
  const edgeRadius = clampInt(options.edgeRadius, 1, 5);
  const reduceFactor = Math.max(0, Math.min(1, options.reduceFactor));
  const fringeColorTolerance = Math.max(0, Math.min(442, options.fringeColorTolerance));
  const isolatedMinNeighbors = clampInt(options.isolatedMinNeighbors, 0, 8);

  // 必须复制，不要直接修改入参，避免 React 状态/历史回退出现脏数据。
  let data = new Uint8ClampedArray(imageData.data);

  const validProtectMask = protectMask && protectMask.length === totalPixels ? protectMask : undefined;
  const isProtected = (pixelIndex: number): boolean => validProtectMask?.[pixelIndex] === 1;

  // 1. 清理极低 alpha 噪点。
  for (let p = 0; p < totalPixels; p++) {
    if (isProtected(p)) continue;
    const i = p * 4;
    const a = data[i + 3];
    if (a > 0 && a <= dropAlpha) {
      data[i + 3] = 0;
    }
  }

  // 2. 可选：删除孤立小点。
  if (options.removeIsolated) {
    const toDrop: number[] = [];
    for (let y = 0; y < height; y++) {
      for (let x = 0; x < width; x++) {
        const p = y * width + x;
        if (isProtected(p)) continue;
        const i = p * 4;
        if (data[i + 3] === 0) continue;
        const neighborCount = countVisibleNeighbors(data, width, height, x, y);
        if (neighborCount < isolatedMinNeighbors) {
          toDrop.push(i + 3);
        }
      }
    }
    for (const alphaIndex of toDrop) {
      data[alphaIndex] = 0;
    }
  }

  // 3. 低透明白边/指定色边缘清理。
  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      const p = y * width + x;
      if (isProtected(p)) continue;

      const i = p * 4;
      const r = data[i];
      const g = data[i + 1];
      const b = data[i + 2];
      const a = data[i + 3];

      if (a === 0) continue;
      if (a > fringeAlphaMax) continue;

      const nearTransparentEdge = hasTransparentNeighbor(data, width, height, x, y, edgeRadius);
      if (!nearTransparentEdge) continue;

      const targetMode = options.targetMode || 'both';
      const neutralWhite = (targetMode === 'both' || targetMode === 'white') ? isNeutralWhiteLike(r, g, b, whiteMin, satMax) : false;
      const nearTargetColor = (targetMode === 'both' || targetMode === 'target') ? colorDistance(r, g, b, options.fringeColor) <= fringeColorTolerance : false;

      if (!neutralWhite && !nearTargetColor) continue;

      if (options.fringeMode === 'remove') {
        data[i + 3] = 0;
      } else {
        const nextAlpha = clampByte(a * reduceFactor);
        data[i + 3] = nextAlpha <= dropAlpha ? 0 : nextAlpha;
      }
    }
  }

  // 4. 透明边 RGB 扩边，解决采样白边。只改 alpha=0 像素的 RGB，不改可见像素。
  data = bleedTransparentRGB(data, width, height, options.bleedIterations);

  return new ImageData(data, width, height);
};

export const hexToRgb = (hex: string): RGB => {
  const clean = hex.trim().replace('#', '');
  if (!/^[0-9a-fA-F]{6}$/.test(clean)) return [255, 255, 255];
  return [
    parseInt(clean.slice(0, 2), 16),
    parseInt(clean.slice(2, 4), 16),
    parseInt(clean.slice(4, 6), 16),
  ];
};
