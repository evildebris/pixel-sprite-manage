export type RGB = [number, number, number];

export interface GlowColorSimplifyOptions {
  /**
   * 单个目标颜色，例如从白边内部吸取的 #B8F0EF。
   * 注意：不要默认使用 #FFFFFF。
   */
  targetColor: string;

  /**
   * 可选：多个目标颜色。
   * 如果传了 targetColors，则优先使用 targetColors。
   */
  targetColors?: string[];

  /**
   * 颜色容差。推荐 55 ~ 75。
   */
  tolerance: number;

  /**
   * 只处理 alpha >= minAlpha 的像素。
   * 处理内部杂色时建议 1。
   */
  minAlpha: number;

  /**
   * 只处理亮度 >= minLuma 的像素。
   * 如果只想处理白边高光，可以设置 60~100。
   * 如果想处理更暗的蓝灰过渡，可以设置 20~40。
   */
  minLuma: number;

  /**
   * 只处理亮度 <= maxLuma 的像素。
   * 通常保持 255。
   */
  maxLuma: number;

  /**
   * 归并成多少个亮度色阶。
   * 推荐 5~7。
   */
  bins: number;

  /**
   * 处理强度，0~1。
   * 1 表示完全吸附到归并色。
   * 0.8 表示保留 20% 原色。
   */
  strength: number;

  /**
   * 构建共享 palette 时最多采样多少像素。
   * 防止几百帧动画时数组过大。
   */
  maxSamples: number;
}

export interface GlowColorPaletteResult {
  palette: RGB[];
  matchedPixels: number;
  sampledPixels: number;
}

interface ColorSample {
  rgb: RGB;
  y: number;
}

const clamp255 = (value: number): number => {
  return Math.max(0, Math.min(255, Math.round(value)));
};

const clamp01 = (value: number): number => {
  return Math.max(0, Math.min(1, value));
};

export const parseHexColor = (hex: string): RGB => {
  const raw = hex.trim().replace('#', '');

  if (/^[0-9a-fA-F]{3}$/.test(raw)) {
    const r = raw[0] + raw[0];
    const g = raw[1] + raw[1];
    const b = raw[2] + raw[2];
    return [
      parseInt(r, 16),
      parseInt(g, 16),
      parseInt(b, 16),
    ];
  }

  if (!/^[0-9a-fA-F]{6}$/.test(raw)) {
    throw new Error(`Invalid hex color: ${hex}`);
  }

  return [
    parseInt(raw.slice(0, 2), 16),
    parseInt(raw.slice(2, 4), 16),
    parseInt(raw.slice(4, 6), 16),
  ];
};

export const rgbToHex = (rgb: RGB): string => {
  return (
    '#' +
    rgb
      .map((v) => clamp255(v).toString(16).padStart(2, '0'))
      .join('')
      .toUpperCase()
  );
};

/**
 * Rec. 709 luma.
 * 用于把目标颜色族按亮度排序分 bin。
 */
export const getLuma = (r: number, g: number, b: number): number => {
  return r * 0.2126 + g * 0.7152 + b * 0.0722;
};

/**
 * 对同一颜色族做更稳定的距离判断。
 * 不使用纯 RGB 欧氏距离的原因：
 * 青白光效中，亮度变化非常明显，但色相变化相对小。
 * 这里给亮度一个中等权重，给色度差一个更高权重。
 */
export const perceptualFamilyDistance = (
  r: number,
  g: number,
  b: number,
  target: RGB
): number => {
  const y1 = getLuma(r, g, b);
  const y2 = getLuma(target[0], target[1], target[2]);

  const cr1 = r - y1;
  const cg1 = g - y1;
  const cb1 = b - y1;

  const cr2 = target[0] - y2;
  const cg2 = target[1] - y2;
  const cb2 = target[2] - y2;

  const dy = (y1 - y2) * 0.55;
  const dcr = (cr1 - cr2) * 1.0;
  const dcg = (cg1 - cg2) * 1.0;
  const dcb = (cb1 - cb2) * 1.0;

  return Math.sqrt(dy * dy + dcr * dcr + dcg * dcg + dcb * dcb);
};

const medianNumber = (values: number[]): number => {
  if (values.length === 0) return 0;
  const sorted = [...values].sort((a, b) => a - b);
  return sorted[Math.floor(sorted.length / 2)];
};

const normalizeOptions = (
  options: Partial<GlowColorSimplifyOptions>
): GlowColorSimplifyOptions => {
  return {
    targetColor: options.targetColor ?? '#B8F0EF',
    targetColors: options.targetColors,
    tolerance: options.tolerance ?? 65,
    minAlpha: options.minAlpha ?? 1,
    minLuma: options.minLuma ?? 40,
    maxLuma: options.maxLuma ?? 255,
    bins: options.bins ?? 6,
    strength: options.strength ?? 1.0,
    maxSamples: options.maxSamples ?? 200000,
  };
};

const getTargetRGBs = (options: GlowColorSimplifyOptions): RGB[] => {
  const colors =
    options.targetColors && options.targetColors.length > 0
      ? options.targetColors
      : [options.targetColor];

  return colors.map(parseHexColor);
};

const getMinDistanceToTargets = (
  r: number,
  g: number,
  b: number,
  targets: RGB[]
): number => {
  let minDist = Infinity;

  for (const target of targets) {
    const dist = perceptualFamilyDistance(r, g, b, target);
    if (dist < minDist) {
      minDist = dist;
    }
  }

  return minDist;
};

const isEligiblePixel = (
  data: Uint8ClampedArray,
  offset: number,
  options: GlowColorSimplifyOptions,
  targets: RGB[]
): boolean => {
  const r = data[offset];
  const g = data[offset + 1];
  const b = data[offset + 2];
  const a = data[offset + 3];

  if (a < options.minAlpha) return false;

  const y = getLuma(r, g, b);
  if (y < options.minLuma || y > options.maxLuma) return false;

  const dist = getMinDistanceToTargets(r, g, b, targets);
  return dist <= options.tolerance;
};

/**
 * 从一张或多张 ImageData 构建共享 palette。
 * 批量动画必须使用共享 palette，避免每帧颜色归并结果不同导致闪烁。
 */
export const buildGlowColorPaletteFromImageDatas = (
  imageDatas: ImageData[],
  rawOptions: Partial<GlowColorSimplifyOptions>
): GlowColorPaletteResult => {
  const options = normalizeOptions(rawOptions);
  const targets = getTargetRGBs(options);

  const samples: ColorSample[] = [];
  let matchedPixels = 0;

  for (const imageData of imageDatas) {
    const data = imageData.data;

    for (let i = 0; i < data.length; i += 4) {
      if (!isEligiblePixel(data, i, options, targets)) continue;

      matchedPixels++;

      // 采样上限，避免几百帧时内存过大。
      // 这里采用确定性间隔采样，保证结果可复现。
      if (samples.length < options.maxSamples) {
        const r = data[i];
        const g = data[i + 1];
        const b = data[i + 2];

        samples.push({
          rgb: [r, g, b],
          y: getLuma(r, g, b),
        });
      }
    }
  }

  if (samples.length === 0) {
    return {
      palette: [],
      matchedPixels,
      sampledPixels: 0,
    };
  }

  samples.sort((a, b) => a.y - b.y);

  const binCount = Math.max(2, Math.min(16, Math.min(options.bins, samples.length)));
  const palette: RGB[] = [];

  for (let bin = 0; bin < binCount; bin++) {
    const start = Math.floor((samples.length * bin) / binCount);
    const end = Math.floor((samples.length * (bin + 1)) / binCount);
    const group = samples.slice(start, end);

    if (group.length === 0) continue;

    const rs = group.map((p) => p.rgb[0]);
    const gs = group.map((p) => p.rgb[1]);
    const bs = group.map((p) => p.rgb[2]);

    const color: RGB = [
      clamp255(medianNumber(rs)),
      clamp255(medianNumber(gs)),
      clamp255(medianNumber(bs)),
    ];

    // 去掉过近重复色，避免 UI palette 里出现肉眼一样的色块。
    const duplicate = palette.some((existing) => {
      const d = Math.sqrt(
        Math.pow(existing[0] - color[0], 2) +
        Math.pow(existing[1] - color[1], 2) +
        Math.pow(existing[2] - color[2], 2)
      );
      return d < 2.5;
    });

    if (!duplicate) {
      palette.push(color);
    }
  }

  return {
    palette,
    matchedPixels,
    sampledPixels: samples.length,
  };
};

const findNearestPaletteColor = (
  r: number,
  g: number,
  b: number,
  palette: RGB[]
): RGB => {
  const y = getLuma(r, g, b);

  let best = palette[0];
  let bestScore = Infinity;

  for (const color of palette) {
    const py = getLuma(color[0], color[1], color[2]);

    const lumaDiff = Math.abs(y - py);
    const familyDiff = perceptualFamilyDistance(r, g, b, color);

    // 同一色族里优先保持亮度层级稳定。
    const score = lumaDiff * 1.25 + familyDiff * 0.35;

    if (score < bestScore) {
      bestScore = score;
      best = color;
    }
  }

  return best;
};

/**
 * 应用 Glow Color Simplify。
 *
 * 注意：
 * 1. 不修改 Alpha。
 * 2. 不删除像素。
 * 3. 不做 blur。
 * 4. 不做 dithering。
 * 5. 只处理目标颜色族内的 RGB。
 */
export const applyGlowColorSimplifyToImageData = (
  imageData: ImageData,
  palette: RGB[],
  rawOptions: Partial<GlowColorSimplifyOptions>
): ImageData => {
  if (palette.length === 0) return imageData;

  const options = normalizeOptions(rawOptions);
  const targets = getTargetRGBs(options);
  const strength = clamp01(options.strength);

  const source = imageData.data;
  const output = new Uint8ClampedArray(source);

  for (let i = 0; i < output.length; i += 4) {
    if (!isEligiblePixel(output, i, options, targets)) continue;

    const r = output[i];
    const g = output[i + 1];
    const b = output[i + 2];
    const a = output[i + 3];

    const nearest = findNearestPaletteColor(r, g, b, palette);

    output[i] = clamp255(r + (nearest[0] - r) * strength);
    output[i + 1] = clamp255(g + (nearest[1] - g) * strength);
    output[i + 2] = clamp255(b + (nearest[2] - b) * strength);

    // Alpha 必须保持不变。
    output[i + 3] = a;
  }

  return new ImageData(output, imageData.width, imageData.height);
};

/**
 * 调试辅助：统计目标颜色族内有多少不同 RGB。
 * 用于验证处理前后颜色是否真的减少。
 */
export const countGlowColorSimplifyStats = (
  imageData: ImageData,
  rawOptions: Partial<GlowColorSimplifyOptions>
): {
  eligiblePixels: number;
  uniqueColors: number;
} => {
  const options = normalizeOptions(rawOptions);
  const targets = getTargetRGBs(options);
  const data = imageData.data;

  let eligiblePixels = 0;
  const colors = new Set<string>();

  for (let i = 0; i < data.length; i += 4) {
    if (!isEligiblePixel(data, i, options, targets)) continue;

    eligiblePixels++;
    colors.add(`${data[i]},${data[i + 1]},${data[i + 2]}`);
  }

  return {
    eligiblePixels,
    uniqueColors: colors.size,
  };
};
