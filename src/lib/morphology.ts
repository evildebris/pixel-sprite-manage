export const erode = (mask: Uint8Array, radius: number, width: number, height: number): Uint8Array => {
  const result = new Uint8Array(mask.length);
  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      const idx = y * width + x;
      if (mask[idx] === 0) continue;
      let keep = true;
      for (let dy = -radius; dy <= radius && keep; dy++) {
        for (let dx = -radius; dx <= radius && keep; dx++) {
          const nx = x + dx;
          const ny = y + dy;
          if (nx < 0 || nx >= width || ny < 0 || ny >= height) {
            keep = false;
            break;
          }
          if (mask[ny * width + nx] === 0) {
            keep = false;
          }
        }
      }
      if (keep) result[idx] = 255;
    }
  }
  return result;
};

export const dilate = (mask: Uint8Array, radius: number, width: number, height: number): Uint8Array => {
  const result = new Uint8Array(mask.length);
  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      const idx = y * width + x;
      if (mask[idx] === 255) {
        result[idx] = 255;
        continue;
      }
      let found = false;
      for (let dy = -radius; dy <= radius && !found; dy++) {
        for (let dx = -radius; dx <= radius && !found; dx++) {
          const nx = x + dx;
          const ny = y + dy;
          if (nx >= 0 && nx < width && ny >= 0 && ny < height) {
            if (mask[ny * width + nx] === 255) {
              found = true;
            }
          }
        }
      }
      if (found) result[idx] = 255;
    }
  }
  return result;
};

export const defaultTrimapForImage = (
  imgData: ImageData,
  transparentColor: string | null,
  tolerance: number,
  pureGlowMode: boolean = false,
  glowRadiusVal: number = 4
): Uint8Array => {
  const width = imgData.width;
  const height = imgData.height;
  const data = imgData.data;
  const trimap = new Uint8Array(width * height);
  
  let bgR = 0, bgG = 0, bgB = 0;
  if (transparentColor) {
    bgR = parseInt(transparentColor.slice(1, 3), 16);
    bgG = parseInt(transparentColor.slice(3, 5), 16);
    bgB = parseInt(transparentColor.slice(5, 7), 16);
  }

  // 1. 提取黑底/近似背景层像素
  const isBlack = new Uint8Array(width * height);
  for (let idx = 0; idx < width * height; idx++) {
    const pIdx = idx * 4;
    const rawAlpha = data[pIdx + 3];
    if (rawAlpha === 0) {
      isBlack[idx] = 1;
      continue;
    }
    if (transparentColor) {
      const dist = Math.sqrt((data[pIdx] - bgR)**2 + (data[pIdx+1] - bgG)**2 + (data[pIdx+2] - bgB)**2);
      if (dist <= tolerance) {
        isBlack[idx] = 1;
      }
    }
  }

  // 2. 利用智能连通域算法，彻底区分“外部背景”与“角色内暗部(如眼睛/暗部轮廓)”
  const visited = new Uint8Array(width * height);
  const componentIds = new Int32Array(width * height);
  componentIds.fill(-1);
  const components: { size: number; connectedToBorder: boolean }[] = [];

  for (let idx = 0; idx < width * height; idx++) {
    if (isBlack[idx] === 1 && visited[idx] === 0) {
      const compId = components.length;
      let size = 0;
      let connectedToBorder = false;

      // BFS 队列搜寻
      const queue: number[] = [idx];
      visited[idx] = 1;
      componentIds[idx] = compId;

      let head = 0;
      while (head < queue.length) {
        const curr = queue[head++];
        size++;

        const cx = curr % width;
        const cy = Math.floor(curr / width);

        if (cx === 0 || cx === width - 1 || cy === 0 || cy === height - 1) {
          connectedToBorder = true;
        }

        const neighbors = [curr - 1, curr + 1, curr - width, curr + width];
        const isLeft = (cx === 0);
        const isRight = (cx === width - 1);

        for (let n = 0; n < 4; n++) {
          const neighborIdx = neighbors[n];
          if (n === 0 && isLeft) continue;
          if (n === 1 && isRight) continue;

          if (neighborIdx >= 0 && neighborIdx < width * height) {
            if (isBlack[neighborIdx] === 1 && visited[neighborIdx] === 0) {
              visited[neighborIdx] = 1;
              componentIds[neighborIdx] = compId;
              queue.push(neighborIdx);
            }
          }
        }
      }

      components.push({ size, connectedToBorder });
    }
  }

  // 3. 构建临时非背景前景蒙版 (包含角色主体 + 外围发光)
  const foregroundMask = new Uint8Array(width * height);
  for (let idx = 0; idx < width * height; idx++) {
    const pIdx = idx * 4;
    const rawAlpha = data[pIdx + 3];
    if (rawAlpha === 0) continue;

    if (transparentColor) {
      if (isBlack[idx] === 1) {
        const compId = componentIds[idx];
        const comp = components[compId];
        // 如果是连通到边缘的大块背景，标记为纯背景
        if (comp && (comp.connectedToBorder || comp.size > 80)) {
          continue;
        }
      }
    }
    foregroundMask[idx] = 255;
  }

  // 4. 数学形态学剥离：对高亮及外部发光进行侵蚀 (Erosion)。
  // 侵蚀半径直接由用户设置的 glowRadiusVal 控制。越往外的发光，由于靠近背景边缘，会被率先剥离出去。
  // 哪怕发光通道亮如水晶，在几何上它们依然属于“边缘发光”，从而被精确归入 128 发光层！
  // 角色扎实的核心则保持在最里层，完美归入 255 纯实心。
  const radius = Math.max(1, Math.min(12, Math.round(glowRadiusVal)));
  const erodedMask = erode(foregroundMask, radius, width, height);

  // 5. 生成最终带有自适应空间分离的 Trimap 数组
  for (let idx = 0; idx < width * height; idx++) {
    if (foregroundMask[idx] === 0) {
      trimap[idx] = 0; // 纯背景
    } else if (erodedMask[idx] === 255) {
      trimap[idx] = 255; // 100% 绝对保护的角色主体原图部分 (Erosion 后的幸存核心)
    } else {
      trimap[idx] = 128; // 自发光、发散辉光、星芒、烟雾特效发光区 (因靠近边缘被剥离)
    }
  }

  return trimap;
};

/**
 * Intelligent client-side AI image matting (Saliency Edge Detection / Border isolation)
 * Analyses image corners to extract background color, and isolates the foreground sprite.
 */
export const smartBorderSaliencyMatting = (
  imgData: ImageData,
  cleaningStrength: number
): ImageData => {
  const width = imgData.width;
  const height = imgData.height;
  const data = imgData.data;

  // We sample 4 corners to estimate background color
  const samplePixels = [
    [0, 0],
    [width - 1, 0],
    [0, height - 1],
    [width - 1, height - 1]
  ];

  let sumR = 0, sumG = 0, sumB = 0, count = 0;
  for (const [x, y] of samplePixels) {
    const idx = (y * width + x) * 4;
    if (data[idx + 3] > 10) {
      sumR += data[idx];
      sumG += data[idx + 1];
      sumB += data[idx + 2];
      count++;
    }
  }

  // Fallback to white/black if background is already transparent
  const estBgR = count > 0 ? Math.round(sumR / count) : 30;
  const estBgG = count > 0 ? Math.round(sumG / count) : 30;
  const estBgB = count > 0 ? Math.round(sumB / count) : 30;

  class FloodFill {
    visited = new Uint8Array(width * height);
    run() {
      const queue: [number, number][] = [];
      // Push borders
      for (let x = 0; x < width; x++) {
        queue.push([x, 0], [x, height - 1]);
      }
      for (let y = 1; y < height - 1; y++) {
        queue.push([0, y], [width - 1, y]);
      }

      let head = 0;
      while (head < queue.length) {
        const [cx, cy] = queue[head++];
        const idx = cy * width + cx;
        if (this.visited[idx]) continue;
        this.visited[idx] = 1;

        const pIdx = idx * 4;
        const currentAlpha = data[pIdx + 3];
        if (currentAlpha === 0) continue;

        // Compare color
        const dist = Math.sqrt(
          Math.pow(data[pIdx] - estBgR, 2) +
          Math.pow(data[pIdx + 1] - estBgG, 2) +
          Math.pow(data[pIdx + 2] - estBgB, 2)
        );

        if (dist < cleaningStrength + 15) {
          data[pIdx + 3] = 0; // Remove matching background
          const neighbors = [
            [cx + 1, cy],
            [cx - 1, cy],
            [cx, cy + 1],
            [cx, cy - 1]
          ];
          for (const [nx, ny] of neighbors) {
            if (nx >= 0 && nx < width && ny >= 0 && ny < height) {
              const nidx = ny * width + nx;
              if (!this.visited[nidx]) queue.push([nx, ny]);
            }
          }
        }
      }
    }
  }

  const filler = new FloodFill();
  filler.run();

  return imgData;
};
