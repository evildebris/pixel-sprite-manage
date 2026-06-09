import React, { useState, useRef, useEffect } from 'react';
import { 
  Upload, 
  Download, 
  Play, 
  Pause, 
  Trash2, 
  Layers, 
  Monitor,
  Zap,
  Loader2,
  Sparkles,
  Languages,
  Pipette,
  Lock,
  Unlock,
  Check,
  X,
  RefreshCw,
  Brush,
  Eraser,
  Files,
  Folder,
  Undo,
  RotateCcw
} from 'lucide-react';
import { motion, AnimatePresence } from 'motion/react';
import JSZip from 'jszip';
import { cn } from './lib/utils';
import { SpriteFrame, AppTab, Language, PreviewMode, BlendMode, BackdropColor } from './types';
import { i18n } from './lib/i18n';
import { erode, dilate, defaultTrimapForImage, smartBorderSaliencyMatting } from './lib/morphology';

const createClassicMattingWorker = () => {
  const workerBlobCode = `
    self.onmessage = function(e) {
      const { action, id, index, imgDataArray, outWidth, outHeight } = e.data;
      
      const data = imgDataArray;
      const width = outWidth;
      const height = outHeight;

      if (action === 'consolidate') {
        const { quantizationTolerance } = e.data;
        const colorCounts = new Map();

        for (let j = 0; j < data.length; j += 4) {
          if (data[j + 3] === 0) continue;
          const key = data[j] + ',' + data[j+1] + ',' + data[j+2];
          colorCounts.set(key, (colorCounts.get(key) || 0) + 1);
        }

        const uniqueColors = Array.from(colorCounts.keys()).map(function(k) {
          return k.split(',').map(Number);
        });
        const colorMap = new Map();
        const processed = new Set();

        uniqueColors.sort(function(a, b) {
          const keyA = a.join(',');
          const keyB = b.join(',');
          return (colorCounts.get(keyB) || 0) - (colorCounts.get(keyA) || 0);
        });

        for (let cIdx = 0; cIdx < uniqueColors.length; cIdx++) {
          const color = uniqueColors[cIdx];
          const key = color.join(',');
          if (processed.has(key)) continue;

          const baseColor = color;
          processed.add(key);
          colorMap.set(key, baseColor);

          for (let oIdx = 0; oIdx < uniqueColors.length; oIdx++) {
            const other = uniqueColors[oIdx];
            const otherKey = other.join(',');
            if (processed.has(otherKey)) continue;

            const dist = Math.sqrt(
              Math.pow(baseColor[0] - other[0], 2) +
              Math.pow(baseColor[1] - other[1], 2) +
              Math.pow(baseColor[2] - other[2], 2)
            );

            if (dist < quantizationTolerance) {
              processed.add(otherKey);
              colorMap.set(otherKey, baseColor);
            }
          }
        }

        for (let j = 0; j < data.length; j += 4) {
          if (data[j + 3] === 0) continue;
          const key = data[j] + ',' + data[j+1] + ',' + data[j+2];
          const finalColor = colorMap.get(key);
          if (finalColor) {
            data[j] = finalColor[0];
            data[j+1] = finalColor[1];
            data[j+2] = finalColor[2];
          }
        }

        self.postMessage({ id, index, imgDataArray, outWidth, outHeight }, [imgDataArray.buffer]);
        return;
      }

      if (action === 'repair') {
        const { outlineColor, repairTolerance } = e.data;
        const or = parseInt(outlineColor.slice(1, 3), 16);
        const og = parseInt(outlineColor.slice(3, 5), 16);
        const ob = parseInt(outlineColor.slice(5, 7), 16);

        const isOutline = function(tx, ty) {
          if (tx < 0 || tx >= width || ty < 0 || ty >= height) return false;
          const i = (ty * width + tx) * 4;
          if (data[i + 3] === 0) return false;
          const dist = Math.sqrt(Math.pow(data[i] - or, 2) + Math.pow(data[i+1] - og, 2) + Math.pow(data[i+2] - ob, 2));
          return dist < repairTolerance;
        };

        for (let i = 0; i < data.length; i += 4) {
          if (data[i + 3] === 0) continue;
          const brightness = (data[i] + data[i+1] + data[i+2]) / 3;
          const dist = Math.sqrt(Math.pow(data[i] - or, 2) + Math.pow(data[i+1] - og, 2) + Math.pow(data[i+2] - ob, 2));
          
          if (dist < repairTolerance * 0.75 || brightness < (repairTolerance * 0.5)) {
            data[i] = or;
            data[i + 1] = og;
            data[i + 2] = ob;
          }
        }

        const additions = [];
        for (let y = 0; y < height; y++) {
          for (let x = 0; x < width; x++) {
            const i = (y * width + x) * 4;
            if (data[i + 3] !== 0) continue;

            const neighbors = [[x-1,y],[x+1,y],[x,y-1],[x,y+1]];
            let touchesInnerSprite = false;
            for (let nIdx = 0; nIdx < neighbors.length; nIdx++) {
              const nx = neighbors[nIdx][0];
              const ny = neighbors[nIdx][1];
              if (nx < 0 || nx >= width || ny < 0 || ny >= height) continue;
              const ni = (ny * width + nx) * 4;
              if (data[ni+3] > 0 && !isOutline(nx, ny)) {
                touchesInnerSprite = true;
                break;
              }
            }
            if (touchesInnerSprite) additions.push(i);
          }
        }

        for (let ai = 0; ai < additions.length; ai++) {
          const idx = additions[ai];
          data[idx] = or;
          data[idx + 1] = og;
          data[idx + 2] = ob;
          data[idx + 3] = 255;
        }

        const gapChanges = [];
        for (let y = 0; y < height; y++) {
          for (let x = 0; x < width; x++) {
            const i = (y * width + x) * 4;
            if (data[i + 3] !== 0) continue;

            const hMatch = isOutline(x - 1, y) && isOutline(x + 1, y);
            const vMatch = isOutline(x, y - 1) && isOutline(x, y + 1);

            if (hMatch || vMatch) {
              gapChanges.push(i);
            }
          }
        }

        for (let gi = 0; gi < gapChanges.length; gi++) {
          const idx = gapChanges[gi];
          data[idx] = or;
          data[idx + 1] = og;
          data[idx + 2] = ob;
          data[idx + 3] = 255;
        }

        self.postMessage({ id, index, imgDataArray, outWidth, outHeight }, [imgDataArray.buffer]);
        return;
      }

      // Default/fallback action is 'keying'
      const { transparentColor, tolerance, masterPalette, videoKeyMethod } = e.data;

      if (videoKeyMethod === 'classic') {
        if (transparentColor) {
          const r = parseInt(transparentColor.slice(1, 3), 16);
          const g = parseInt(transparentColor.slice(3, 5), 16);
          const b = parseInt(transparentColor.slice(5, 7), 16);

          const isBackgroundMatch = function(dr, dg, db) {
            return dr < tolerance && dg < tolerance && db < tolerance;
          };

          if (!masterPalette) {
            const quantStep = 24; 
            for (let i = 0; i < data.length; i += 4) {
              data[i] = Math.round(data[i] / quantStep) * quantStep;
              data[i+1] = Math.round(data[i+1] / quantStep) * quantStep;
              data[i+2] = Math.round(data[i+2] / quantStep) * quantStep;
            }
          }

          // Direct global color keying removal, as requested by the user
          for (let i = 0; i < data.length; i += 4) {
            const dr = Math.abs(data[i] - r);
            const dg = Math.abs(data[i + 1] - g);
            const db = Math.abs(data[i + 2] - b);
            if (isBackgroundMatch(dr, dg, db)) {
              data[i + 3] = 0;
            }
          }

          if (masterPalette && masterPalette.length > 0) {
            for (let i = 0; i < data.length; i += 4) {
              if (data[i + 3] === 0) continue;
              let minDist = Infinity;
              let bestColor = [data[i], data[i+1], data[i+2]];
              for (let cIdx = 0; cIdx < masterPalette.length; cIdx++) {
                const color = masterPalette[cIdx];
                const dist = Math.sqrt(
                  Math.pow(data[i] - color[0], 2) +
                  Math.pow(data[i+1] - color[1], 2) +
                  Math.pow(data[i+2] - color[2], 2)
                );
                if (dist < minDist) {
                  minDist = dist;
                  bestColor = color;
                }
              }
              data[i] = bestColor[0];
              data[i+1] = bestColor[1];
              data[i+2] = bestColor[2];
            }
          }

          const isSolid = function(tx, ty) {
            if (tx < 0 || tx >= width || ty < 0 || ty >= height) return false;
            return data[(ty * width + tx) * 4 + 3] > 0;
          };

          const pixelsToRemove = [];
          for (let y = 0; y < height; y++) {
            for (let x = 0; x < width; x++) {
              const i = (y * width + x) * 4;
              if (data[i + 3] === 0) continue;
              let neighbors = 0;
              for (let dy = -1; dy <= 1; dy++) {
                for (let dx = -1; dx <= 1; dx++) {
                  if (dx === 0 && dy === 0) continue;
                  if (isSolid(x + dx, y + dy)) neighbors++;
                }
              }
              if (neighbors === 0) pixelsToRemove.push(i + 3);
            }
          }
          for (let pi = 0; pi < pixelsToRemove.length; pi++) {
            data[pixelsToRemove[pi]] = 0;
          }
        }
      } else {
        const samplePixels = [
          [0, 0],
          [width - 1, 0],
          [0, height - 1],
          [width - 1, height - 1]
        ];

        let sumR = 0, sumG = 0, sumB = 0, count = 0;
        for (let sIdx = 0; sIdx < samplePixels.length; sIdx++) {
          const sx = samplePixels[sIdx][0];
          const sy = samplePixels[sIdx][1];
          const idx = (sy * width + sx) * 4;
          if (data[idx + 3] > 10) {
            sumR += data[idx];
            sumG += data[idx + 1];
            sumB += data[idx + 2];
            count++;
          }
        }

        const estBgR = count > 0 ? Math.round(sumR / count) : 30;
        const estBgG = count > 0 ? Math.round(sumG / count) : 30;
        const estBgB = count > 0 ? Math.round(sumB / count) : 30;

        // Direct global color keying removal based on estimated background color
        for (let i = 0; i < data.length; i += 4) {
          const currentAlpha = data[i + 3];
          if (currentAlpha === 0) continue;

          const dist = Math.sqrt(
            Math.pow(data[i] - estBgR, 2) +
            Math.pow(data[i + 1] - estBgG, 2) +
            Math.pow(data[i + 2] - estBgB, 2)
          );

          if (dist < tolerance + 15) {
            data[i + 3] = 0; 
          }
        }
      }

      self.postMessage({ id, index, imgDataArray, outWidth, outHeight }, [imgDataArray.buffer]);
    };
  `;
  const blob = new Blob([workerBlobCode], { type: 'application/javascript' });
  return new Worker(URL.createObjectURL(blob));
};

export default function App() {
  // Localization & Root View
  const [lang, setLang] = useState<Language>('zh');
  const [currentTab, setCurrentTab] = useState<AppTab>('video');

  // Shared frames cache
  const [frames, setFrames] = useState<SpriteFrame[]>([]);
  const [rawFrames, setRawFrames] = useState<SpriteFrame[]>([]);
  const [quantizedFrames, setQuantizedFrames] = useState<SpriteFrame[]>([]);

  // Edge Cleanup History Stack
  const [cleanupHistory, setCleanupHistory] = useState<SpriteFrame[][]>([]);
  const [initialCleanupState, setInitialCleanupState] = useState<SpriteFrame[]>([]);

  // Video Extraction states
  const [videoFile, setVideoFile] = useState<File | null>(null);
  const [videoUrl, setVideoUrl] = useState<string>('');
  const [isProcessing, setIsProcessing] = useState(false);
  const [isQuantizing, setIsQuantizing] = useState(false);
  const [isRepairing, setIsRepairing] = useState(false);
  const [isDragging, setIsDragging] = useState(false);
  const [progress, setProgress] = useState(0);
  const [scaleFactor, setScaleFactor] = useState(6);
  const [transparentColor, setTransparentColor] = useState<string | null>('#000000');
  const [colorLocalInput, setColorLocalInput] = useState('000000');
  const [tolerance, setTolerance] = useState(15);
  const [paletteLock, setPaletteLock] = useState(true);
  const [outlineColor, setOutlineColor] = useState('#000000');
  const [repairTolerance, setRepairTolerance] = useState(80);
  const [quantizationTolerance, setQuantizationTolerance] = useState(12);
  const [previewIndex, setPreviewIndex] = useState(0);
  const [isPreviewing, setIsPreviewing] = useState(false);
  const [videoDimensions, setVideoDimensions] = useState({ width: 0, height: 0 });
  const [fps, setFps] = useState(12);

  // Batch Image States
  const [batchFiles, setBatchFiles] = useState<File[]>([]);
  const [batchKeyMethod, setBatchKeyMethod] = useState<'classic' | 'ai'>('classic');
  const [videoKeyMethod, setVideoKeyMethod] = useState<'classic' | 'ai'>('classic');
  const [concurrency, setConcurrency] = useState<number>(10);
  const [isBatchRunning, setIsBatchRunning] = useState(false);

  // Translucent Matting states
  const [brushMode, setBrushMode] = useState<'fg' | 'bg' | 'unknown'>('fg');
  const [trimapBrushSize, setTrimapBrushSize] = useState(8);
  const [activePreviewMode, setActivePreviewMode] = useState<PreviewMode>('final');
  const [coreTolerance, setCoreTolerance] = useState(18);
  const [glowRadiusVal, setGlowRadiusVal] = useState(4);
  const [glowBlendMode, setGlowBlendMode] = useState<BlendMode>('screen');
  const [pureGlowMode, setPureGlowMode] = useState(false);
  const [gameDualExportChecked, setGameDualExportChecked] = useState(true);
  const [trimaps, setTrimaps] = useState<{[idx: number]: Uint8Array}>({});
  const [isDrawingTrimap, setIsDrawingTrimap] = useState(false);
  const [isMattingSequence, setIsMattingSequence] = useState(false);

  // Local active previews dynamic generators
  const [currentTrimapDataUrl, setCurrentTrimapDataUrl] = useState<string>('');
  const [currentCoreDataUrl, setCurrentCoreDataUrl] = useState<string>('');
  const [currentGlowDataUrl, setCurrentGlowDataUrl] = useState<string>('');
  const [currentFinalDataUrl, setCurrentFinalDataUrl] = useState<string>('');

  // Edge Cleanup States
  const [cleanupBGMock, setCleanupBGMock] = useState<BackdropColor>('transparent');
  const [stainColor, setStainColor] = useState('#ffffff');
  const [cleanupStrength, setCleanupStrength] = useState(30);
  const [stainPipetteActive, setStainPipetteActive] = useState(false);
  const [cleanupProtectActive, setCleanupProtectActive] = useState(false);
  const [protectMasks, setProtectMasks] = useState<{[idx: number]: Uint8Array}>({});
  const [cleanupBrushSize, setCleanupBrushSize] = useState(8);
  const [isDrawingProtect, setIsDrawingProtect] = useState(false);
  const [isCleaningProgress, setIsCleaningProgress] = useState(false);

  const videoRef = useRef<HTMLVideoElement>(null);
  const canvasRef = useRef<HTMLCanvasElement>(null);
  const previewTimerRef = useRef<number | null>(null);

  // Auto-play animation previews loop
  useEffect(() => {
    if (isPreviewing && frames.length > 0) {
      previewTimerRef.current = window.setInterval(() => {
        setPreviewIndex((prev) => (prev + 1) % frames.length);
      }, 1000 / fps);
    } else {
      if (previewTimerRef.current) clearInterval(previewTimerRef.current);
    }
    return () => {
      if (previewTimerRef.current) clearInterval(previewTimerRef.current);
    };
  }, [isPreviewing, frames.length, fps]);

  useEffect(() => {
    if (transparentColor) {
      setColorLocalInput(transparentColor.replace('#', '').toUpperCase());
    } else {
      setColorLocalInput('');
    }
  }, [transparentColor]);

  // Recalculates trans matting previews on setting adjustments
  useEffect(() => {
    if (frames.length > 0 && currentTab === 'translucent') {
      triggerActivePreviewRecalc();
    }
  }, [
    previewIndex, 
    currentTab, 
    coreTolerance, 
    glowRadiusVal, 
    glowBlendMode, 
    pureGlowMode,
    trimaps, 
    transparentColor, 
    tolerance, 
    frames
  ]);

  // Edge Cleanup initialization to preserve cleanable state and handle reset/revert
  useEffect(() => {
    if (currentTab === 'cleanup') {
      setInitialCleanupState([...frames]);
      setCleanupHistory([]);
    }
  }, [currentTab, frames.length]); // reset/init if frames list changes or tab moves into cleanup

  // Translate labels helper
  const t = (key: keyof typeof i18n['zh']) => {
    return i18n[lang][key] || i18n['zh'][key] || String(key);
  };

  const handleFileChange = (e: React.ChangeEvent<HTMLInputElement>) => {
    const file = e.target.files?.[0];
    if (file) loadVideo(file);
  };

  const loadVideo = (file: File) => {
    setVideoFile(file);
    const url = URL.createObjectURL(file);
    setVideoUrl(url);
    setFrames([]);
    setRawFrames([]);
    setQuantizedFrames([]);
    setProgress(0);
    setPreviewIndex(0);
    setIsPreviewing(false);
    setCurrentTab('video');
  };

  const handleInitialMultipleUpload = (fileList: FileList | null) => {
    if (!fileList || fileList.length === 0) return;
    const files = Array.from(fileList);
    const video = files.find(f => f.type.startsWith('video/'));
    if (video) {
      loadVideo(video);
    } else {
      const images = files.filter(f => f.type.startsWith('image/'));
      if (images.length > 0) {
        loadImagesAsFrames(images);
      }
    }
  };

  const loadImagesAsFrames = async (files: File[]) => {
    setIsProcessing(true);
    setFrames([]);
    setRawFrames([]);
    setQuantizedFrames([]);
    setProgress(0);
    setPreviewIndex(0);

    const imageFiles = [...files].sort((a, b) => a.name.localeCompare(b.name, undefined, { numeric: true, sensitivity: 'base' }));

    if (imageFiles.length === 0) {
      setIsProcessing(false);
      return;
    }

    try {
      // Set sample dimensions using first image
      const sampleImg = new Image();
      sampleImg.src = URL.createObjectURL(imageFiles[0]);
      await new Promise((resolve) => { sampleImg.onload = resolve; });
      setVideoDimensions({ width: sampleImg.width, height: sampleImg.height });

      interface LocalProcessedItem {
        id: string;
        index: number;
        dataUrl: string;
        blob: Blob;
        rawDataUrl: string;
      }

      const processedFrames = await mapConcurrent<File, LocalProcessedItem>(
        imageFiles,
        concurrency,
        async (file, idx) => {
          const url = URL.createObjectURL(file);
          const img = new Image();
          img.src = url;
          await new Promise((resolve) => { img.onload = resolve; });

          const canvas = document.createElement('canvas');
          const ctx = canvas.getContext('2d', { willReadFrequently: true });
          if (!ctx) throw new Error("Parallel canvas creation failed");

          const outWidth = Math.max(1, Math.floor(img.width / scaleFactor));
          const outHeight = Math.max(1, Math.floor(img.height / scaleFactor));
          canvas.width = outWidth;
          canvas.height = outHeight;

          ctx.imageSmoothingEnabled = false;
          ctx.clearRect(0, 0, outWidth, outHeight);
          ctx.drawImage(img, 0, 0, img.width, img.height, 0, 0, outWidth, outHeight);

          // Capture raw pristine frame reference (No quantization/lossy transparency)
          const rawDataUrl = canvas.toDataURL('image/png');

          const imgData = ctx.getImageData(0, 0, outWidth, outHeight);
          const imgDataArray = new Uint8ClampedArray(imgData.data.buffer);

          const w = createClassicMattingWorker();
          const outcomeArray = await new Promise<Uint8ClampedArray>((resolveW) => {
            w.onmessage = (event) => {
              resolveW(event.data.imgDataArray);
              w.terminate();
            };
            w.postMessage({
              id: crypto.randomUUID(),
              index: idx,
              imgDataArray,
              outWidth,
              outHeight,
              transparentColor,
              tolerance,
              masterPalette: null,
              videoKeyMethod
            }, [imgDataArray.buffer]);
          });

          const outcomeImgData = new ImageData(outcomeArray, outWidth, outHeight);
          ctx.putImageData(outcomeImgData, 0, 0);

          const dataUrl = canvas.toDataURL('image/png');
          const blob = await new Promise<Blob | null>((resolve) => canvas.toBlob(resolve, 'image/png'));
          if (!blob) throw new Error("Image loader blob conversion failed");

          return {
            id: `${file.name}-${idx}`,
            index: idx,
            dataUrl,
            blob,
            rawDataUrl
          };
        }
      );

      const validList = processedFrames.filter(Boolean);
      const rawList: SpriteFrame[] = validList.map(item => ({
        id: item.id,
        index: item.index,
        dataUrl: item.rawDataUrl,
        blob: item.blob
      }));

      const processedList: SpriteFrame[] = validList.map(item => ({
        id: item.id,
        index: item.index,
        dataUrl: item.dataUrl,
        blob: item.blob
      }));

      setFrames(processedList);
      setRawFrames(rawList);
      setProgress(0);
      setCurrentTab('translucent'); // Immediately jump to translucent editing as powerful default
    } catch (err) {
      console.error("Error loading images as frames: ", err);
    } finally {
      setIsProcessing(false);
    }
  };

  const onVideoLoaded = (e: React.SyntheticEvent<HTMLVideoElement>) => {
    const video = e.currentTarget;
    setVideoDimensions({ width: video.videoWidth, height: video.videoHeight });
  };

  // Video Classic Extraction
  const processVideo = async () => {
    if (!videoRef.current || !canvasRef.current) return;

    setIsProcessing(true);
    setFrames([]);
    setRawFrames([]);
    setQuantizedFrames([]);
    setProgress(0);
    setPreviewIndex(0);

    try {
      const video = videoRef.current;
      const canvas = canvasRef.current;
      const ctx = canvas.getContext('2d', { willReadFrequently: true });
      
      if (!ctx) return;

      const outWidth = Math.max(1, Math.floor(video.videoWidth / scaleFactor));
      const outHeight = Math.max(1, Math.floor(video.videoHeight / scaleFactor));
      canvas.width = outWidth;
      canvas.height = outHeight;

      const rawFrameList: SpriteFrame[] = [];
      const processedFrameList: SpriteFrame[] = [];
      const duration = video.duration;
      const totalFrames = Math.max(1, Math.floor(duration * fps));
      const step = 1 / fps;

      video.pause();
      let masterPalette: number[][] | null = null;

      interface FrameTask {
        id: string;
        index: number;
        rawDataUrl: string;
        imgDataArray: Uint8ClampedArray;
      }

      const tasks: FrameTask[] = [];

      // Phase 1: High-speed frame extraction & caching on main thread
      for (let i = 0; i < totalFrames; i++) {
        video.currentTime = i * step;
        
        await new Promise<void>((resolve) => {
          const onSeeked = () => {
            video.removeEventListener('seeked', onSeeked);
            resolve();
          };
          video.addEventListener('seeked', onSeeked);
        });

        ctx.imageSmoothingEnabled = false;
        ctx.clearRect(0, 0, outWidth, outHeight);
        ctx.drawImage(video, 0, 0, video.videoWidth, video.videoHeight, 0, 0, outWidth, outHeight);

        const rawDataUrl = canvas.toDataURL('image/png');
        const imgData = ctx.getImageData(0, 0, outWidth, outHeight);
        const imgDataArray = new Uint8ClampedArray(imgData.data.buffer);

        if (i === 0 && videoKeyMethod === 'classic' && transparentColor && paletteLock) {
          masterPalette = extractPalette(ctx, outWidth, outHeight, transparentColor, tolerance);
        }

        tasks.push({
          id: crypto.randomUUID(),
          index: i,
          rawDataUrl,
          imgDataArray
        });

        setProgress(Math.round(((i + 1) / totalFrames) * 15)); // Allocate 15% progress to frame rendering
      }

      // Phase 2: Parallel Web Worker processing pool
      let taskIdx = 0;
      let finishedCount = 0;

      await new Promise<void>((resolveDone) => {
        if (tasks.length === 0) {
          resolveDone();
          return;
        }

        const maxConcurrency = Math.min(concurrency, tasks.length);
        const activeWorkers = Array.from({ length: maxConcurrency }, () => {
          const w = createClassicMattingWorker();

          w.onmessage = async (event) => {
            const { index, imgDataArray } = event.data;
            const origTask = tasks[index];

            // Render output to secondary temporary canvas
            const tempCanvas = document.createElement('canvas');
            tempCanvas.width = outWidth;
            tempCanvas.height = outHeight;
            const tempCtx = tempCanvas.getContext('2d');
            if (tempCtx) {
              const resImgData = new ImageData(imgDataArray, outWidth, outHeight);
              tempCtx.putImageData(resImgData, 0, 0);
            }

            const processedDataUrl = tempCanvas.toDataURL('image/png');
            const processedBlob = await new Promise<Blob | null>((resolveBlob) => tempCanvas.toBlob(resolveBlob, 'image/png'));
            const finalBlob = processedBlob || new Blob();

            processedFrameList.push({
              id: origTask.id,
              dataUrl: processedDataUrl,
              blob: finalBlob,
              index: index
            });

            rawFrameList.push({
              id: origTask.id,
              dataUrl: origTask.rawDataUrl,
              blob: finalBlob,
              index: index
            });

            finishedCount++;
            setProgress(Math.round(15 + (finishedCount / tasks.length) * 85)); // 15% to 100%

            if (taskIdx < tasks.length) {
              const nextTask = tasks[taskIdx++];
              w.postMessage({
                id: nextTask.id,
                index: nextTask.index,
                imgDataArray: nextTask.imgDataArray,
                outWidth,
                outHeight,
                transparentColor,
                tolerance,
                masterPalette,
                videoKeyMethod
              }, [nextTask.imgDataArray.buffer]);
            } else {
              w.terminate();
              if (finishedCount === tasks.length) {
                resolveDone();
              }
            }
          };

          return w;
        });

        // Seed initial tasks
        for (const w of activeWorkers) {
          if (taskIdx < tasks.length) {
            const nextTask = tasks[taskIdx++];
            w.postMessage({
              id: nextTask.id,
              index: nextTask.index,
              imgDataArray: nextTask.imgDataArray,
              outWidth,
              outHeight,
              transparentColor,
              tolerance,
              masterPalette,
              videoKeyMethod
            }, [nextTask.imgDataArray.buffer]);
          }
        }
      });

      // Maintain user chronological sorting
      processedFrameList.sort((a, b) => a.index - b.index);
      rawFrameList.sort((a, b) => a.index - b.index);

      setRawFrames(rawFrameList);
      setFrames(processedFrameList);
      setQuantizedFrames([]);
    } catch (err) {
      console.error("Error processing video frames: ", err);
    } finally {
      setIsProcessing(false);
    }
  };

  const extractPalette = (ctx: CanvasRenderingContext2D, width: number, height: number, targetHex: string, removalTolerance: number) => {
    const imageData = ctx.getImageData(0, 0, width, height);
    const data = imageData.data;
    const r = parseInt(targetHex.slice(1, 3), 16);
    const g = parseInt(targetHex.slice(3, 5), 16);
    const b = parseInt(targetHex.slice(5, 7), 16);

    const colors = new Set<string>();
    const palette: number[][] = [];

    for (let i = 0; i < data.length; i += 4) {
      const dr = Math.abs(data[i] - r);
      const dg = Math.abs(data[i + 1] - g);
      const db = Math.abs(data[i + 2] - b);

      if (dr < removalTolerance && dg < removalTolerance && db < removalTolerance) continue;

      const key = `${data[i]},${data[i + 1]},${data[i + 2]}`;
      if (!colors.has(key)) {
        colors.add(key);
        palette.push([data[i], data[i + 1], data[i + 2]]);
      }
    }
    return palette;
  };

  const cleanPixelArt = (
    ctx: CanvasRenderingContext2D, 
    width: number, 
    height: number, 
    targetHex: string, 
    removalTolerance: number,
    palette: number[][] | null
  ) => {
    const imageData = ctx.getImageData(0, 0, width, height);
    const data = imageData.data;
    
    const r = parseInt(targetHex.slice(1, 3), 16);
    const g = parseInt(targetHex.slice(3, 5), 16);
    const b = parseInt(targetHex.slice(5, 7), 16);

    const isBackgroundMatch = (dr: number, dg: number, db: number) => {
      return dr < removalTolerance && dg < removalTolerance && db < removalTolerance;
    };

    if (!palette) {
      const quantStep = 24; 
      for (let i = 0; i < data.length; i += 4) {
        data[i] = Math.round(data[i] / quantStep) * quantStep;
        data[i+1] = Math.round(data[i+1] / quantStep) * quantStep;
        data[i+2] = Math.round(data[i+2] / quantStep) * quantStep;
      }
    }

    const visited = new Uint8ClampedArray(width * height);
    const queue: [number, number][] = [];
    for (let x = 0; x < width; x++) queue.push([x, 0], [x, height - 1]);
    for (let y = 1; y < height - 1; y++) queue.push([0, y], [width - 1, y]);

    let head = 0;
    while (head < queue.length) {
      const [cx, cy] = queue[head++];
      const vIdx = cy * width + cx;
      if (visited[vIdx]) continue;
      visited[vIdx] = 1;

      const dIdx = vIdx * 4;
      const dr = Math.abs(data[dIdx] - r);
      const dg = Math.abs(data[dIdx + 1] - g);
      const db = Math.abs(data[dIdx + 2] - b);

      if (isBackgroundMatch(dr, dg, db)) {
        data[dIdx + 3] = 0; 
        const neighbors = [[cx + 1, cy], [cx - 1, cy], [cx, cy + 1], [cx, cy - 1]];
        for (const [nx, ny] of neighbors) {
          if (nx >= 0 && nx < width && ny >= 0 && ny < height && !visited[ny * width + nx]) queue.push([nx, ny]);
        }
      }
    }

    if (palette && palette.length > 0) {
      for (let i = 0; i < data.length; i += 4) {
        if (data[i + 3] === 0) continue;
        let minDist = Infinity;
        let bestColor = [data[i], data[i+1], data[i+2]];
        for (const color of palette) {
          const dist = Math.sqrt(
            Math.pow(data[i] - color[0], 2) +
            Math.pow(data[i+1] - color[1], 2) +
            Math.pow(data[i+2] - color[2], 2)
          );
          if (dist < minDist) {
            minDist = dist;
            bestColor = color;
          }
        }
        data[i] = bestColor[0];
        data[i+1] = bestColor[1];
        data[i+2] = bestColor[2];
      }
    }

    const isSolid = (tx: number, ty: number) => {
      if (tx < 0 || tx >= width || ty < 0 || ty >= height) return false;
      return data[(ty * width + tx) * 4 + 3] > 0;
    };

    const pixelsToRemove: number[] = [];
    for (let y = 0; y < height; y++) {
      for (let x = 0; x < width; x++) {
        const i = (y * width + x) * 4;
        if (data[i + 3] === 0) continue;
        let neighbors = 0;
        for (let dy = -1; dy <= 1; dy++) {
          for (let dx = -1; dx <= 1; dx++) {
            if (dx === 0 && dy === 0) continue;
            if (isSolid(x + dx, y + dy)) neighbors++;
          }
        }
        if (neighbors === 0) pixelsToRemove.push(i + 3);
      }
    }
    for (const alphaIdx of pixelsToRemove) data[alphaIdx] = 0;
    
    ctx.putImageData(imageData, 0, 0);
  };

  // Color consolidation handler
  const consolidateColors = async () => {
    const sourceFrames = frames.length > 0 ? frames : rawFrames;
    if (sourceFrames.length === 0) return;
    setIsQuantizing(true);
    setProgress(0);

    const newFrames = await mapConcurrent<SpriteFrame, SpriteFrame>(
      sourceFrames,
      concurrency,
      async (frame, i) => {
        const img = new Image();
        img.src = frame.dataUrl;
        
        await new Promise((resolve) => { img.onload = resolve; });

        const canvas = document.createElement('canvas');
        const ctx = canvas.getContext('2d', { willReadFrequently: true });
        if (!ctx) throw new Error("Could not construct parallel canvas ctx");

        canvas.width = img.width;
        canvas.height = img.height;
        ctx.clearRect(0, 0, canvas.width, canvas.height);
        ctx.drawImage(img, 0, 0);

        const imageData = ctx.getImageData(0, 0, canvas.width, canvas.height);
        const imgDataArray = new Uint8ClampedArray(imageData.data.buffer);

        const w = createClassicMattingWorker();
        const outcomeArray = await new Promise<Uint8ClampedArray>((resolveW) => {
          w.onmessage = (event) => {
            resolveW(event.data.imgDataArray);
            w.terminate();
          };
          w.postMessage({
            action: 'consolidate',
            id: crypto.randomUUID(),
            index: i,
            imgDataArray,
            outWidth: canvas.width,
            outHeight: canvas.height,
            quantizationTolerance
          }, [imgDataArray.buffer]);
        });

        const finalImgData = new ImageData(outcomeArray, canvas.width, canvas.height);
        ctx.putImageData(finalImgData, 0, 0);

        const blob = await new Promise<Blob | null>((resolve) => canvas.toBlob(resolve, 'image/png'));
        if (!blob) throw new Error("Consolidation blob conversion failed");

        // Report incremental progress safely
        setProgress((prev) => Math.min(99, Math.round(prev + (1 / sourceFrames.length) * 100)));

        return {
          ...frame,
          dataUrl: canvas.toDataURL('image/png'),
          blob
        };
      }
    );

    const validFrames = newFrames.filter(Boolean);
    setQuantizedFrames(validFrames);
    setFrames(validFrames);
    setIsQuantizing(false);
    setProgress(0);
  };

  // Outline Edge Repair
  const repairExtractedFrames = async () => {
    const sourceFrames = quantizedFrames.length > 0 ? quantizedFrames : (frames.length > 0 ? frames : rawFrames);
    if (sourceFrames.length === 0) return;
    
    setIsRepairing(true);
    setProgress(0);

    const repaired = await mapConcurrent<SpriteFrame, SpriteFrame>(
      sourceFrames,
      concurrency,
      async (frame, i) => {
        const img = new Image();
        img.src = frame.dataUrl;
        await new Promise((resolve) => { img.onload = resolve; });

        const localCanvas = document.createElement('canvas');
        localCanvas.width = img.width;
        localCanvas.height = img.height;
        const localCtx = localCanvas.getContext('2d', { willReadFrequently: true });
        if (!localCtx) throw new Error("Local canvas failed for repair");

        localCtx.clearRect(0, 0, localCanvas.width, localCanvas.height);
        localCtx.drawImage(img, 0, 0);

        const imageData = localCtx.getImageData(0, 0, localCanvas.width, localCanvas.height);
        const imgDataArray = new Uint8ClampedArray(imageData.data.buffer);

        const w = createClassicMattingWorker();
        const outcomeArray = await new Promise<Uint8ClampedArray>((resolveW) => {
          w.onmessage = (event) => {
            resolveW(event.data.imgDataArray);
            w.terminate();
          };
          w.postMessage({
            action: 'repair',
            id: crypto.randomUUID(),
            index: i,
            imgDataArray,
            outWidth: localCanvas.width,
            outHeight: localCanvas.height,
            outlineColor,
            repairTolerance
          }, [imgDataArray.buffer]);
        });

        const finalImgData = new ImageData(outcomeArray, localCanvas.width, localCanvas.height);
        localCtx.putImageData(finalImgData, 0, 0);

        const blob = await new Promise<Blob | null>((resolve) => localCanvas.toBlob(resolve, 'image/png'));
        if (!blob) throw new Error("Failed to export blob in repair parallel execution");

        // Report incremental progress safely
        setProgress((prev) => Math.min(99, Math.round(prev + (1 / sourceFrames.length) * 100)));

        return {
          ...frame,
          dataUrl: localCanvas.toDataURL('image/png'),
          blob
        };
      }
    );

    const validRepaired = repaired.filter(Boolean);
    setFrames(validRepaired);
    setIsRepairing(false);
    setProgress(0);
  };

  const enhancedOutlineRepair = (
    ctx: CanvasRenderingContext2D, 
    width: number, 
    height: number, 
    targetOutlineHex: string,
    tolerance: number
  ) => {
    const imageData = ctx.getImageData(0, 0, width, height);
    const data = imageData.data;
    
    const or = parseInt(targetOutlineHex.slice(1, 3), 16);
    const og = parseInt(targetOutlineHex.slice(3, 5), 16);
    const ob = parseInt(targetOutlineHex.slice(5, 7), 16);

    const isOutline = (tx: number, ty: number) => {
      if (tx < 0 || tx >= width || ty < 0 || ty >= height) return false;
      const i = (ty * width + tx) * 4;
      if (data[i + 3] === 0) return false;
      const dist = Math.sqrt(Math.pow(data[i] - or, 2) + Math.pow(data[i+1] - og, 2) + Math.pow(data[i+2] - ob, 2));
      return dist < tolerance;
    };

    for (let i = 0; i < data.length; i += 4) {
      if (data[i + 3] === 0) continue;
      const brightness = (data[i] + data[i+1] + data[i+2]) / 3;
      const dist = Math.sqrt(Math.pow(data[i] - or, 2) + Math.pow(data[i+1] - og, 2) + Math.pow(data[i+2] - ob, 2));
      
      if (dist < tolerance * 0.75 || brightness < (tolerance * 0.5)) {
        data[i] = or;
        data[i + 1] = og;
        data[i + 2] = ob;
      }
    }

    const additions: number[] = [];
    for (let y = 0; y < height; y++) {
      for (let x = 0; x < width; x++) {
        const i = (y * width + x) * 4;
        if (data[i + 3] !== 0) continue;

        const neighbors = [[x-1,y],[x+1,y],[x,y-1],[x,y+1]];
        let touchesInnerSprite = false;
        for (const [nx, ny] of neighbors) {
          if (nx < 0 || nx >= width || ny < 0 || ny >= height) continue;
          const ni = (ny * width + nx) * 4;
          if (data[ni+3] > 0 && !isOutline(nx, ny)) {
            touchesInnerSprite = true;
            break;
          }
        }
        if (touchesInnerSprite) additions.push(i);
      }
    }

    for (const idx of additions) {
      data[idx] = or;
      data[idx + 1] = og;
      data[idx + 2] = ob;
      data[idx + 3] = 255;
    }

    const gapChanges: number[] = [];
    for (let y = 0; y < height; y++) {
      for (let x = 0; x < width; x++) {
        const i = (y * width + x) * 4;
        if (data[i + 3] !== 0) continue;

        const hMatch = isOutline(x - 1, y) && isOutline(x + 1, y);
        const vMatch = isOutline(x, y - 1) && isOutline(x, y + 1);

        if (hMatch || vMatch) {
          gapChanges.push(i);
        }
      }
    }

    for (const idx of gapChanges) {
      data[idx] = or;
      data[idx + 1] = og;
      data[idx + 2] = ob;
      data[idx + 3] = 255;
    }
    
    ctx.putImageData(imageData, 0, 0);
  };

  // Batch Image uploads
  const handleBatchImageUpload = async (e: React.ChangeEvent<HTMLInputElement>) => {
    const filesList = e.target.files;
    if (!filesList || filesList.length === 0) return;

    setBatchFiles(Array.from(filesList));
    setFrames([]);
    setRawFrames([]);
    setQuantizedFrames([]);
    setProgress(0);
    setPreviewIndex(0);
  };

  // Helper for parallel worker processing with concurrency limits (max 15, default 10)
  const mapConcurrent = async <T, R>(
    items: T[],
    concurrencyLimit: number,
    fn: (item: T, idx: number) => Promise<R>
  ): Promise<R[]> => {
    const results: R[] = new Array(items.length);
    let currentIndex = 0;
    let doneCount = 0;

    const runWorker = async () => {
      while (currentIndex < items.length) {
        const idx = currentIndex;
        currentIndex++;
        const item = items[idx];
        try {
          results[idx] = await fn(item, idx);
        } catch (err) {
          console.error("Worker error at index", idx, err);
        }
        doneCount++;
        setProgress(Math.round((doneCount / items.length) * 100));
      }
    };

    const workers = [];
    const count = Math.min(concurrencyLimit, items.length);
    for (let i = 0; i < count; i++) {
      workers.push(runWorker());
    }
    await Promise.all(workers);
    return results;
  };

  // Run Batch Image Process
  const executeBatchProcess = async () => {
    if (batchFiles.length === 0) return;
    setIsBatchRunning(true);
    setProgress(0);

    const frameList: SpriteFrame[] = await mapConcurrent<File, SpriteFrame>(
      batchFiles,
      concurrency,
      async (file, i) => {
        const img = new Image();
        img.src = URL.createObjectURL(file);
        
        await new Promise((resolve) => { img.onload = resolve; });

        const canvas = document.createElement('canvas');
        const ctx = canvas.getContext('2d', { willReadFrequently: true });
        if (!ctx) {
          throw new Error("Could not construct parallel canvas ctx");
        }

        // Determine size (apply custom scaling if requested, or keep native pixel dimensions)
        const outWidth = Math.max(1, Math.floor(img.width / scaleFactor));
        const outHeight = Math.max(1, Math.floor(img.height / scaleFactor));
        canvas.width = outWidth;
        canvas.height = outHeight;

        ctx.imageSmoothingEnabled = false;
        ctx.clearRect(0, 0, outWidth, outHeight);
        ctx.drawImage(img, 0, 0, img.width, img.height, 0, 0, outWidth, outHeight);

        const imgData = ctx.getImageData(0, 0, outWidth, outHeight);
        const imgDataArray = new Uint8ClampedArray(imgData.data.buffer);

        const w = createClassicMattingWorker();
        const outcomeArray = await new Promise<Uint8ClampedArray>((resolveW) => {
          w.onmessage = (event) => {
            resolveW(event.data.imgDataArray);
            w.terminate();
          };
          w.postMessage({
            id: crypto.randomUUID(),
            index: i,
            imgDataArray,
            outWidth,
            outHeight,
            transparentColor,
            tolerance,
            masterPalette: null,
            videoKeyMethod: batchKeyMethod
          }, [imgDataArray.buffer]);
        });

        const finalImgData = new ImageData(outcomeArray, outWidth, outHeight);
        ctx.putImageData(finalImgData, 0, 0);

        const blob = await new Promise<Blob | null>((resolve) => canvas.toBlob(resolve, 'image/png'));
        if (!blob) throw new Error("Blob conversion failed");

        return {
          id: crypto.randomUUID(),
          dataUrl: canvas.toDataURL('image/png'),
          blob,
          index: i
        };
      }
    );

    const validFrames = frameList.filter(Boolean).sort((a, b) => a.index - b.index);

    setFrames(validFrames);
    setRawFrames(validFrames);
    setIsBatchRunning(false);
    setProgress(0);
  };

  // Generate Automatic Trimap on Demand
  const autoBuildActiveTrimap = () => {
    if (frames.length === 0) return;
    const frame = frames[previewIndex];
    if (!frame) return;

    const img = new Image();
    img.src = frame.dataUrl;
    img.onload = () => {
      const canvas = document.createElement('canvas');
      canvas.width = img.width;
      canvas.height = img.height;
      const ctx = canvas.getContext('2d');
      if (!ctx) return;
      ctx.drawImage(img, 0, 0);
      const imgData = ctx.getImageData(0, 0, canvas.width, canvas.height);
      const trimap = defaultTrimapForImage(imgData, transparentColor, tolerance, pureGlowMode, glowRadiusVal);
      
      setTrimaps(prev => ({
        ...prev,
        [previewIndex]: trimap
      }));
    };
  };

  // Recalculates dynamically Core, Glow, and Final previews
  const triggerActivePreviewRecalc = () => {
    if (rawFrames.length === 0 || rawFrames.length <= previewIndex) return;
    const rawFrame = rawFrames[previewIndex];
    const img = new Image();
    img.src = rawFrame.dataUrl;
    img.onload = () => {
      const canvas = document.createElement('canvas');
      canvas.width = img.width;
      canvas.height = img.height;
      const ctx = canvas.getContext('2d');
      if (!ctx) return;
      ctx.drawImage(img, 0, 0);
      const imgData = ctx.getImageData(0, 0, canvas.width, canvas.height);
      const rawData = imgData.data;

      // Find or default trimap
      let trimap = trimaps[previewIndex];
      if (!trimap) {
        trimap = defaultTrimapForImage(imgData, transparentColor, tolerance, pureGlowMode, glowRadiusVal);
      }

      const width = canvas.width;
      const height = canvas.height;

      // 1. Trimap visualization (overlay FG=green, BG=red, Unknown=blue)
      const trimapCanvas = document.createElement('canvas');
      trimapCanvas.width = width;
      trimapCanvas.height = height;
      const tCtx = trimapCanvas.getContext('2d');
      if (tCtx) {
        tCtx.drawImage(img, 0, 0);
        const tImgData = tCtx.getImageData(0, 0, width, height);
        const tData = tImgData.data;
        for (let j = 0; j < trimap.length; j++) {
          const tVal = trimap[j];
          const pxIdx = j * 4;
          if (tVal === 255) { // Foreground
            tData[pxIdx] = Math.round(tData[pxIdx] * 0.4 + 34 * 0.6);
            tData[pxIdx+1] = Math.round(tData[pxIdx+1] * 0.4 + 197 * 0.6);
            tData[pxIdx+2] = Math.round(tData[pxIdx+2] * 0.4 + 94 * 0.6);
          } else if (tVal === 0) { // Background
            tData[pxIdx] = Math.round(tData[pxIdx] * 0.3 + 239 * 0.7);
            tData[pxIdx+1] = Math.round(tData[pxIdx+1] * 0.3 + 68 * 0.7);
            tData[pxIdx+2] = Math.round(tData[pxIdx+2] * 0.3 + 68 * 0.7);
          } else if (tVal === 128) { // Unknown
            tData[pxIdx] = Math.round(tData[pxIdx] * 0.4 + 59 * 0.6);
            tData[pxIdx+1] = Math.round(tData[pxIdx+1] * 0.4 + 130 * 0.6);
            tData[pxIdx+2] = Math.round(tData[pxIdx+2] * 0.4 + 246 * 0.6);
          }
        }
        tCtx.putImageData(tImgData, 0, 0);
        setCurrentTrimapDataUrl(trimapCanvas.toDataURL('image/png'));
      }

      // 2. Translucent matting formulas (Core vs Glow)
      const coreCanvas = document.createElement('canvas');
      coreCanvas.width = width;
      coreCanvas.height = height;
      const cCtx = coreCanvas.getContext('2d');

      const glowCanvas = document.createElement('canvas');
      glowCanvas.width = width;
      glowCanvas.height = height;
      const gCtx = glowCanvas.getContext('2d');

      const finalCanvas = document.createElement('canvas');
      finalCanvas.width = width;
      finalCanvas.height = height;
      const fCtx = finalCanvas.getContext('2d');

      if (cCtx && gCtx && fCtx) {
        const cImg = cCtx.createImageData(width, height);
        const cData = cImg.data;

        const gImg = gCtx.createImageData(width, height);
        const gData = gImg.data;

        const fImg = fCtx.createImageData(width, height);
        const fData = fImg.data;

        // Extract backdrop key
        let bgR = 0, bgG = 0, bgB = 0;
        if (transparentColor) {
          bgR = parseInt(transparentColor.slice(1, 3), 16);
          bgG = parseInt(transparentColor.slice(3, 5), 16);
          bgB = parseInt(transparentColor.slice(5, 7), 16);
        }

        // Cache FG coordinates for spatial weights
        const fgIndices: number[] = [];
        for (let j = 0; j < trimap.length; j++) {
          if (trimap[j] === 255) fgIndices.push(j);
        }

        const getMinDistToFg = (pIdx: number) => {
          if (fgIndices.length === 0) return 0;
          const py = Math.floor(pIdx / width);
          const px = pIdx % width;
          let minDist = Infinity;
          // Sample index coordinates optimization
          const samples = Math.min(25, fgIndices.length);
          const step = Math.max(1, Math.floor(fgIndices.length / samples));
          for (let s = 0; s < fgIndices.length; s += step) {
            const fPos = fgIndices[s];
            const fY = Math.floor(fPos / width);
            const fX = fPos % width;
            const dist = Math.sqrt((px - fX)**2 + (py - fY)**2);
            if (dist < minDist) minDist = dist;
          }
          return minDist;
        };

        for (let j = 0; j < trimap.length; j++) {
          const tVal = trimap[j];
          const pxIdx = j * 4;
          const rawR = rawData[pxIdx];
          const rawG = rawData[pxIdx+1];
          const rawB = rawData[pxIdx+2];
          const rawA = rawData[pxIdx+3];

          if (rawA === 0) continue;

          // Core alpha and Glow alpha
          let coreAlpha = 0;
          let glowAlpha = 0;

          if (tVal === 255) {
            coreAlpha = pureGlowMode ? 0.0 : 1.0;
            glowAlpha = 1.0;
          } else if (tVal === 0) {
            coreAlpha = 0.0;
            glowAlpha = 0.0;
          } else {
            // Spatial weight formula representation (generous or bypass if maxed out; only computed in Unknown region)
            const d = getMinDistToFg(j);
            const spatialWeight = (glowRadiusVal === 25 || fgIndices.length === 0) ? 1.0 : Math.exp(-d / (glowRadiusVal * 1.5));

            const dist = Math.sqrt((rawR - bgR)**2 + (rawG - bgG)**2 + (rawB - bgB)**2);
            const tLow = tolerance;
            const tHigh = tLow + coreTolerance * 1.5 + 20;

            // 1. Delta Keyer (Core Alpha - 第一步提取纯主体)
            if (pureGlowMode) {
              coreAlpha = 0.0;
            } else {
              if (dist >= tHigh) {
                coreAlpha = 1.0;
              } else if (dist <= tLow) {
                coreAlpha = 0.0;
              } else {
                coreAlpha = (dist - tLow) / (tHigh - tLow);
              }
            }

            // 2. Luma / Channel Mask for Glow (Glow Alpha - 第二步提取半透明光晕与星芒)
            const deltaR = Math.max(0, rawR - bgR);
            const deltaG = Math.max(0, rawG - bgG);
            const deltaB = Math.max(0, rawB - bgB);

            // 亮色最大通道作为发光物理不透明度的极限基准值
            const numMax = Math.max(deltaR, Math.max(deltaG, deltaB));
            const glowScore = numMax;

            // 完美的物理自发光百分比不透明度
            let physicalBaseAlpha = numMax / 255.0;

            // 黄金三次 Hermite 插值剔除暗部低能噪声
            if (numMax <= tolerance) {
              physicalBaseAlpha = 0;
            } else if (numMax < tolerance + 35) {
              const tValInterpolate = (numMax - tolerance) / 35;
              physicalBaseAlpha = physicalBaseAlpha * (3 * tValInterpolate * tValInterpolate - 2 * tValInterpolate * tValInterpolate * tValInterpolate);
            }

            // 让用户滑块对光能起到补充微调作用，但防止把半透明错误膨胀到 1.0
            const lowThreshold = Math.max(5, tolerance * 0.4);
            const highThreshold = Math.max(lowThreshold + 55, 185 - coreTolerance * 1.5);
            let glowAlphaBaseSlider = 0;
            if (glowScore <= lowThreshold) {
              glowAlphaBaseSlider = 0.0;
            } else if (glowScore >= highThreshold) {
              glowAlphaBaseSlider = 1.0;
            } else {
              glowAlphaBaseSlider = (glowScore - lowThreshold) / (highThreshold - lowThreshold);
            }

            // 完美的黄金加权公式：85% 绝对物理，15% 结合用户调节，彻底分离黑底与光尘效果
            const finalGlowAlphaBase = physicalBaseAlpha * 0.85 + (physicalBaseAlpha * glowAlphaBaseSlider) * 0.15;

            // 空间衰减系数：高亮度的自发光星芒点可无视距离彻底还原
            const scoreFactor = Math.min(1.0, (glowScore * glowScore) / 900.0);
            const finalSpatialWeight = Math.max(spatialWeight, scoreFactor);
            glowAlpha = Math.min(1.0, finalGlowAlphaBase * finalSpatialWeight);
          }

          // Core RGBA
          if (coreAlpha > 0) {
            const cr = Math.max(0, Math.min(255, (rawR - (1 - coreAlpha) * bgR) / coreAlpha));
            const cg = Math.max(0, Math.min(255, (rawG - (1 - coreAlpha) * bgG) / coreAlpha));
            const cb = Math.max(0, Math.min(255, (rawB - (1 - coreAlpha) * bgB) / coreAlpha));
            cData[pxIdx] = Math.round(cr);
            cData[pxIdx+1] = Math.round(cg);
            cData[pxIdx+2] = Math.round(cb);
            cData[pxIdx+3] = Math.round(coreAlpha * 255);
          } else {
            cData[pxIdx] = 0;
            cData[pxIdx+1] = 0;
            cData[pxIdx+2] = 0;
            cData[pxIdx+3] = 0;
          }

          // Glow RGBA
          if (glowAlpha > 0) {
            const gr = Math.max(0, Math.min(255, (rawR - (1 - glowAlpha) * bgR) / glowAlpha));
            const gg = Math.max(0, Math.min(255, (rawG - (1 - glowAlpha) * bgG) / glowAlpha));
            const gb = Math.max(0, Math.min(255, (rawB - (1 - glowAlpha) * bgB) / glowAlpha));
            gData[pxIdx] = Math.round(gr);
            gData[pxIdx+1] = Math.round(gg);
            gData[pxIdx+2] = Math.round(gb);
            gData[pxIdx+3] = Math.round(glowAlpha * 255);
          } else {
            gData[pxIdx] = 0;
            gData[pxIdx+1] = 0;
            gData[pxIdx+2] = 0;
            gData[pxIdx+3] = 0;
          }

          // 3. Synthesis and De-black / Unpremultiply (第三步 融合融合与完美去黑)
          let synthesisCoreAlpha = coreAlpha;
          if (pureGlowMode) {
            if (tVal === 255) {
              synthesisCoreAlpha = 1.0;
            } else if (tVal === 0) {
              synthesisCoreAlpha = 0.0;
            } else {
              const dist = Math.sqrt((rawR - bgR)**2 + (rawG - bgG)**2 + (rawB - bgB)**2);
              const tLow = tolerance;
              const tHigh = tLow + coreTolerance * 1.5 + 20;
              if (dist >= tHigh) {
                synthesisCoreAlpha = 1.0;
              } else if (dist <= tLow) {
                synthesisCoreAlpha = 0.0;
              } else {
                synthesisCoreAlpha = (dist - tLow) / (tHigh - tLow);
              }
            }
          }

          const finalAlpha = Math.max(synthesisCoreAlpha, glowAlpha);
          let finalR = rawR;
          let finalG = rawG;
          let finalB = rawB;

          if (finalAlpha > 0 && synthesisCoreAlpha < 0.98) {
            // 进行无暇的反预乘物理计算，提取出极亮的前景原色
            const unpremPower = Math.max(0.01, finalAlpha);
            const r_unprem = (rawR - bgR * (1 - finalAlpha)) / unpremPower;
            const g_unprem = (rawG - bgG * (1 - finalAlpha)) / unpremPower;
            const b_unprem = (rawB - bgB * (1 - finalAlpha)) / unpremPower;

            finalR = Math.max(0, Math.min(255, r_unprem));
            finalG = Math.max(0, Math.min(255, g_unprem));
            finalB = Math.max(0, Math.min(255, b_unprem));
          }

          if (synthesisCoreAlpha >= 0.98) {
            // Guarantee original color pixels are preserved perfectly for character cores (No brightness changes)
            fData[pxIdx] = rawR;
            fData[pxIdx+1] = rawG;
            fData[pxIdx+2] = rawB;
            fData[pxIdx+3] = Math.round(synthesisCoreAlpha * 255);
          } else {
            // 写入在任何正常混合棋盘格上都能100%渲染出通透无黑气的自发光发散前景和不透明度
            fData[pxIdx] = Math.round(finalR);
            fData[pxIdx+1] = Math.round(finalG);
            fData[pxIdx+2] = Math.round(finalB);
            fData[pxIdx+3] = Math.round(finalAlpha * 255);
          }
        }

        cCtx.putImageData(cImg, 0, 0);
        gCtx.putImageData(gImg, 0, 0);
        fCtx.putImageData(fImg, 0, 0);

        setCurrentCoreDataUrl(coreCanvas.toDataURL('image/png'));
        setCurrentGlowDataUrl(glowCanvas.toDataURL('image/png'));
        setCurrentFinalDataUrl(finalCanvas.toDataURL('image/png'));
      }
    };
  };

  // Perform translucent matting on everything using concurrent mapping workers
  const executeTranslucentMattingSeq = async () => {
    if (rawFrames.length === 0) return;
    setIsMattingSequence(true);
    setProgress(0);

    // Reset single frame previews instantly so that active preview shows live update clearly
    setCurrentCoreDataUrl('');
    setCurrentGlowDataUrl('');
    setCurrentFinalDataUrl('');

    const compiledFrames: SpriteFrame[] = await mapConcurrent<SpriteFrame, SpriteFrame>(
      rawFrames,
      concurrency,
      async (frame, i) => {
        const img = new Image();
        img.src = frame.dataUrl;

        await new Promise((resolve) => { img.onload = resolve; });

        const localCanvas = document.createElement('canvas');
        localCanvas.width = img.width;
        localCanvas.height = img.height;
        const localCtx = localCanvas.getContext('2d', { willReadFrequently: true });
        if (!localCtx) throw new Error("Local canvas creation failed for matting");

        localCtx.clearRect(0, 0, img.width, img.height);
        localCtx.drawImage(img, 0, 0);

        const imgData = localCtx.getImageData(0, 0, localCanvas.width, localCanvas.height);
        const rawData = imgData.data;

        // Access or auto fallback trimap (Only preserve active previewIndex trimap to allow parameter adjustments and repeat runs of video sequence translucent matting)
        let trimap = (frame.index === previewIndex) ? trimaps[previewIndex] : null;
        if (!trimap) {
          trimap = defaultTrimapForImage(imgData, transparentColor, tolerance, pureGlowMode, glowRadiusVal);
        }

        // Generate Core, Glow, and final merged arrays
        const cImg = localCtx.createImageData(localCanvas.width, localCanvas.height);
        const cData = cImg.data;
        const gImg = localCtx.createImageData(localCanvas.width, localCanvas.height);
        const gData = gImg.data;
        const fImg = localCtx.createImageData(localCanvas.width, localCanvas.height);
        const fData = fImg.data;

        let bgR = 0, bgG = 0, bgB = 0;
        if (transparentColor) {
          bgR = parseInt(transparentColor.slice(1, 3), 16);
          bgG = parseInt(transparentColor.slice(3, 5), 16);
          bgB = parseInt(transparentColor.slice(5, 7), 16);
        }

        // Core distance calculators
        const fgPoints: number[] = [];
        for (let j = 0; j < trimap.length; j++) {
          if (trimap[j] === 255) fgPoints.push(j);
        }

        const getLocalMinDistToFg = (pIdx: number) => {
          if (fgPoints.length === 0) return 0;
          const py = Math.floor(pIdx / localCanvas.width);
          const px = pIdx % localCanvas.width;
          let minDist = Infinity;
          const samples = Math.min(25, fgPoints.length);
          const sampleStep = Math.max(1, Math.floor(fgPoints.length / samples));
          for (let s = 0; s < fgPoints.length; s += sampleStep) {
            const fIdx = fgPoints[s];
            const fY = Math.floor(fIdx / localCanvas.width);
            const fX = fIdx % localCanvas.width;
            const d = Math.sqrt((px - fX)**2 + (py - fY)**2);
            if (d < minDist) minDist = d;
          }
          return minDist;
        };

        for (let j = 0; j < trimap.length; j++) {
          const tVal = trimap[j];
          const pxIdx = j * 4;
          const rawR = rawData[pxIdx];
          const rawG = rawData[pxIdx+1];
          const rawB = rawData[pxIdx+2];
          const rawA = rawData[pxIdx+3];

          if (rawA === 0) continue;

          // Core alpha and Glow alpha
          let coreAlpha = 0;
          let glowAlpha = 0;

          if (tVal === 255) {
            coreAlpha = pureGlowMode ? 0.0 : 1.0;
            glowAlpha = 1.0;
          } else if (tVal === 0) {
            coreAlpha = 0.0;
            glowAlpha = 0.0;
          } else {
            // Spatial weight formula representation (only computed in Unknown region)
            const minDist = getLocalMinDistToFg(j);
            const spatialWeight = (glowRadiusVal === 25 || fgPoints.length === 0) ? 1.0 : Math.exp(-minDist / (glowRadiusVal * 1.5));

            const dist = Math.sqrt((rawR - bgR)**2 + (rawG - bgG)**2 + (rawB - bgB)**2);
            const tLow = tolerance;
            const tHigh = tLow + coreTolerance * 1.5 + 20;

            // 1. Delta Keyer (Core Alpha - 第一步提取纯主体)
            if (pureGlowMode) {
              coreAlpha = 0.0;
            } else {
              if (dist >= tHigh) {
                coreAlpha = 1.0;
              } else if (dist <= tLow) {
                coreAlpha = 0.0;
              } else {
                coreAlpha = (dist - tLow) / (tHigh - tLow);
              }
            }

            // 2. Luma / Channel Mask for Glow (Glow Alpha - 提取半透明发光与星芒)
            const deltaR = Math.max(0, rawR - bgR);
            const deltaG = Math.max(0, rawG - bgG);
            const deltaB = Math.max(0, rawB - bgB);

            // 亮色最大通道作为发光物理不透明度的极限基准值
            const numMax = Math.max(deltaR, Math.max(deltaG, deltaB));
            const glowScore = numMax;

            // 完美的物理自发光百分比不透明度
            let physicalBaseAlpha = numMax / 255.0;

            // 黄金三次 Hermite 插值剔除暗部低能噪声
            if (numMax <= tolerance) {
              physicalBaseAlpha = 0;
            } else if (numMax < tolerance + 35) {
              const tValInterpolate = (numMax - tolerance) / 35;
              physicalBaseAlpha = physicalBaseAlpha * (3 * tValInterpolate * tValInterpolate - 2 * tValInterpolate * tValInterpolate * tValInterpolate);
            }

            // 让用户滑块对光能起到补充微调作用，但防止把半透明错误膨胀到 1.0
            const lowThreshold = Math.max(5, tolerance * 0.4);
            const highThreshold = Math.max(lowThreshold + 55, 185 - coreTolerance * 1.5);
            let glowAlphaBaseSlider = 0;
            if (glowScore <= lowThreshold) {
              glowAlphaBaseSlider = 0.0;
            } else if (glowScore >= highThreshold) {
              glowAlphaBaseSlider = 1.0;
            } else {
              glowAlphaBaseSlider = (glowScore - lowThreshold) / (highThreshold - lowThreshold);
            }

            // 完美的黄金加权公式：85% 绝对物理，15% 结合用户调节，彻底分离黑底与光尘效果
            const finalGlowAlphaBase = physicalBaseAlpha * 0.85 + (physicalBaseAlpha * glowAlphaBaseSlider) * 0.15;

            // 空间衰减系数：高亮度的自发光星芒点可无视距离彻底还原
            const scoreFactor = Math.min(1.0, (glowScore * glowScore) / 900.0);
            const finalSpatialWeight = Math.max(spatialWeight, scoreFactor);
            glowAlpha = Math.min(1.0, finalGlowAlphaBase * finalSpatialWeight);
          }

          // Fill core
          if (coreAlpha > 0) {
            const cr = Math.max(0, Math.min(255, (rawR - (1 - coreAlpha) * bgR) / coreAlpha));
            const cg = Math.max(0, Math.min(255, (rawG - (1 - coreAlpha) * bgG) / coreAlpha));
            const cb = Math.max(0, Math.min(255, (rawB - (1 - coreAlpha) * bgB) / coreAlpha));
            cData[pxIdx] = Math.round(cr);
            cData[pxIdx+1] = Math.round(cg);
            cData[pxIdx+2] = Math.round(cb);
            cData[pxIdx+3] = Math.round(coreAlpha * 255);
          } else {
            cData[pxIdx] = 0;
            cData[pxIdx+1] = 0;
            cData[pxIdx+2] = 0;
            cData[pxIdx+3] = 0;
          }

          // Fill glow
          if (glowAlpha > 0) {
            const gr = Math.max(0, Math.min(255, (rawR - (1 - glowAlpha) * bgR) / glowAlpha));
            const gg = Math.max(0, Math.min(255, (rawG - (1 - glowAlpha) * bgG) / glowAlpha));
            const gb = Math.max(0, Math.min(255, (rawB - (1 - glowAlpha) * bgB) / glowAlpha));
            gData[pxIdx] = Math.round(gr);
            gData[pxIdx+1] = Math.round(gg);
            gData[pxIdx+2] = Math.round(gb);
            gData[pxIdx+3] = Math.round(glowAlpha * 255);
          } else {
            gData[pxIdx] = 0;
            gData[pxIdx+1] = 0;
            gData[pxIdx+2] = 0;
            gData[pxIdx+3] = 0;
          }

          // 3. Synthesis and De-black / Unpremultiply (合成与去溢色反预乘)
          let synthesisCoreAlpha = coreAlpha;
          if (pureGlowMode) {
            if (tVal === 255) {
              synthesisCoreAlpha = 1.0;
            } else if (tVal === 0) {
              synthesisCoreAlpha = 0.0;
            } else {
              const dist = Math.sqrt((rawR - bgR)**2 + (rawG - bgG)**2 + (rawB - bgB)**2);
              const tLow = tolerance;
              const tHigh = tLow + coreTolerance * 1.5 + 20;
              if (dist >= tHigh) {
                synthesisCoreAlpha = 1.0;
              } else if (dist <= tLow) {
                synthesisCoreAlpha = 0.0;
              } else {
                synthesisCoreAlpha = (dist - tLow) / (tHigh - tLow);
              }
            }
          }

          const finalAlpha = Math.max(synthesisCoreAlpha, glowAlpha);
          let finalR = rawR;
          let finalG = rawG;
          let finalB = rawB;

          if (finalAlpha > 0 && synthesisCoreAlpha < 0.98) {
            // 进行无暇的反预乘物理计算，提取出极亮的前景原色
            const unpremPower = Math.max(0.01, finalAlpha);
            const r_unprem = (rawR - bgR * (1 - finalAlpha)) / unpremPower;
            const g_unprem = (rawG - bgG * (1 - finalAlpha)) / unpremPower;
            const b_unprem = (rawB - bgB * (1 - finalAlpha)) / unpremPower;

            finalR = Math.max(0, Math.min(255, r_unprem));
            finalG = Math.max(0, Math.min(255, g_unprem));
            finalB = Math.max(0, Math.min(255, b_unprem));
          }

          if (synthesisCoreAlpha >= 0.98) {
            // Guarantee original color pixels are preserved perfectly for character cores (No brightness changes)
            fData[pxIdx] = rawR;
            fData[pxIdx+1] = rawG;
            fData[pxIdx+2] = rawB;
            fData[pxIdx+3] = Math.round(synthesisCoreAlpha * 255);
          } else {
            // 写入在任何正常混合棋盘格上都能100%渲染出通透无黑气的自发光发散前景和不透明度
            fData[pxIdx] = Math.round(finalR);
            fData[pxIdx+1] = Math.round(finalG);
            fData[pxIdx+2] = Math.round(finalB);
            fData[pxIdx+3] = Math.round(finalAlpha * 255);
          }
        }

        const outCoreCanv = document.createElement('canvas');
        outCoreCanv.width = localCanvas.width;
        outCoreCanv.height = localCanvas.height;
        outCoreCanv.getContext('2d')?.putImageData(cImg, 0, 0);

        const outGlowCanv = document.createElement('canvas');
        outGlowCanv.width = localCanvas.width;
        outGlowCanv.height = localCanvas.height;
        outGlowCanv.getContext('2d')?.putImageData(gImg, 0, 0);

        const outFinalCanv = document.createElement('canvas');
        outFinalCanv.width = localCanvas.width;
        outFinalCanv.height = localCanvas.height;
        outFinalCanv.getContext('2d')?.putImageData(fImg, 0, 0);

        const finalBlob = await new Promise<Blob | null>((resolve) => outFinalCanv.toBlob(resolve, 'image/png'));
        if (!finalBlob) throw new Error("Failed to export final blob during matting parallel execution");

        return {
          id: frame.id,
          index: frame.index,
          dataUrl: outFinalCanv.toDataURL('image/png'),
          blob: finalBlob,
          coreDataUrl: outCoreCanv.toDataURL('image/png'),
          glowDataUrl: outGlowCanv.toDataURL('image/png')
        };
      }
    );

    const validFrames = compiledFrames.filter(Boolean);
    setFrames(validFrames);
    setIsMattingSequence(false);
    setProgress(0);

    // End of matting sequence, clear caching to allow live loading and immediately force redraw on active frame
    setCurrentCoreDataUrl('');
    setCurrentGlowDataUrl('');
    setCurrentFinalDataUrl('');
    setTimeout(() => {
      triggerActivePreviewRecalc();
    }, 50);
  };

  // Helper handles Pointer Events on canvas to Paint Trimap or Protection masks
  const handleCanvasInteraction = (e: React.MouseEvent<HTMLCanvasElement>) => {
    if (frames.length === 0) return;
    const canvas = e.currentTarget;
    const rect = canvas.getBoundingClientRect();
    const scaleX = canvas.width / rect.width;
    const scaleY = canvas.height / rect.height;
    const x = Math.floor((e.clientX - rect.left) * scaleX);
    const y = Math.floor((e.clientY - rect.top) * scaleY);

    if (x < 0 || x >= canvas.width || y < 0 || y >= canvas.height) return;

    if (currentTab === 'translucent') {
      // Paint Trimap mask
      const trimapVal = brushMode === 'fg' ? 255 : brushMode === 'bg' ? 0 : 128;
      let existingTrimap = trimaps[previewIndex];
      if (!existingTrimap) {
        existingTrimap = new Uint8Array(canvas.width * canvas.height);
        existingTrimap.fill(128); // default to unknown
      }

      const updated = new Uint8Array(existingTrimap);
      const radius = trimapBrushSize;

      for (let dy = -radius; dy <= radius; dy++) {
        for (let dx = -radius; dx <= radius; dx++) {
          if (dx*dx + dy*dy <= radius*radius) {
            const px = x + dx;
            const py = y + dy;
            if (px >= 0 && px < canvas.width && py >= 0 && py < canvas.height) {
              updated[py * canvas.width + px] = trimapVal;
            }
          }
        }
      }

      setTrimaps(prev => ({
        ...prev,
        [previewIndex]: updated
      }));
    } else if (currentTab === 'cleanup') {
      if (stainPipetteActive) {
        // Pipette read color under mouse position from the current active frame image
        const frame = frames[previewIndex];
        if (frame) {
          const img = new Image();
          img.src = frame.dataUrl;
          img.onload = () => {
            const tempCanvas = document.createElement('canvas');
            tempCanvas.width = img.width;
            tempCanvas.height = img.height;
            const tempCtx = tempCanvas.getContext('2d');
            if (tempCtx) {
              tempCtx.drawImage(img, 0, 0);
              const pixel = tempCtx.getImageData(x, y, 1, 1).data;
              const hex = `#${[pixel[0], pixel[1], pixel[2]].map(val => val.toString(16).padStart(2, '0')).join('')}`;
              setStainColor(hex);
              setStainPipetteActive(false);
            }
          };
        }
        return;
      }

      if (cleanupProtectActive) {
        // Paint color protection mask
        let mask = protectMasks[previewIndex];
        if (!mask) {
          mask = new Uint8Array(canvas.width * canvas.height);
        }
        const updated = new Uint8Array(mask);
        const radius = cleanupBrushSize;

        for (let dy = -radius; dy <= radius; dy++) {
          for (let dx = -radius; dx <= radius; dx++) {
            if (dx*dx + dy*dy <= radius*radius) {
              const px = x + dx;
              const py = y + dy;
              if (px >= 0 && px < canvas.width && py >= 0 && py < canvas.height) {
                updated[py * canvas.width + px] = 1; // Protected
              }
            }
          }
        }

        setProtectMasks(prev => ({
          ...prev,
          [previewIndex]: updated
        }));
      }
    }
  };

  // Run noise/stain cleaner on current frame or all frames
  const runStainCleaner = async (allFrames: boolean = false) => {
    if (frames.length === 0) return;
    setIsCleaningProgress(true);

    // Save previous state to history
    setCleanupHistory(prev => [...prev, [...frames]]);

    const matchR = parseInt(stainColor.slice(1, 3), 16);
    const matchG = parseInt(stainColor.slice(3, 5), 16);
    const matchB = parseInt(stainColor.slice(5, 7), 16);

    const updatedFrames = [...frames];

    if (!allFrames) {
      // Just single frame (fast, synchronous)
      const frame = frames[previewIndex];
      const img = new Image();
      img.src = frame.dataUrl;
      await new Promise((resolve) => { img.onload = resolve; });

      const canvas = document.createElement('canvas');
      canvas.width = img.width;
      canvas.height = img.height;
      const ctx = canvas.getContext('2d', { willReadFrequently: true });
      if (ctx) {
        ctx.clearRect(0, 0, img.width, img.height);
        ctx.drawImage(img, 0, 0);
        const imgData = ctx.getImageData(0, 0, canvas.width, canvas.height);
        const data = imgData.data;
        const protect = protectMasks[previewIndex] || new Uint8Array(canvas.width * canvas.height);

        for (let j = 0; j < protect.length; j++) {
          if (protect[j] === 1) continue;
          const pIdx = j * 4;
          const currentA = data[pIdx + 3];
          if (currentA === 0) continue;

          const dist = Math.sqrt(
            Math.pow(data[pIdx] - matchR, 2) +
            Math.pow(data[pIdx + 1] - matchG, 2) +
            Math.pow(data[pIdx + 2] - matchB, 2)
          );

          if (dist <= cleanupStrength) {
            data[pIdx + 3] = 0;
          }
        }
        ctx.putImageData(imgData, 0, 0);
        const blob = await new Promise<Blob | null>((resolve) => canvas.toBlob(resolve, 'image/png'));
        if (blob) {
          updatedFrames[previewIndex] = {
            ...frame,
            dataUrl: canvas.toDataURL('image/png'),
            blob
          };
        }
      }
      setFrames(updatedFrames);
      setIsCleaningProgress(false);
    } else {
      // Parallel batch clean using mapConcurrent!
      const cleaned = await mapConcurrent<SpriteFrame, SpriteFrame>(
        frames,
        concurrency,
        async (frame, i) => {
          const img = new Image();
          img.src = frame.dataUrl;
          await new Promise((resolve) => { img.onload = resolve; });

          const localCanvas = document.createElement('canvas');
          localCanvas.width = img.width;
          localCanvas.height = img.height;
          const localCtx = localCanvas.getContext('2d', { willReadFrequently: true });
          if (!localCtx) throw new Error("Local canvas failed for stain clean");

          localCtx.clearRect(0, 0, img.width, img.height);
          localCtx.drawImage(img, 0, 0);
          const imgData = localCtx.getImageData(0, 0, localCanvas.width, localCanvas.height);
          const data = imgData.data;
          const protect = protectMasks[i] || new Uint8Array(localCanvas.width * localCanvas.height);

          for (let j = 0; j < protect.length; j++) {
            if (protect[j] === 1) continue;
            const pIdx = j * 4;
            const currentA = data[pIdx + 3];
            if (currentA === 0) continue;

            const dist = Math.sqrt(
              Math.pow(data[pIdx] - matchR, 2) +
              Math.pow(data[pIdx + 1] - matchG, 2) +
              Math.pow(data[pIdx + 2] - matchB, 2)
            );

            if (dist <= cleanupStrength) {
              data[pIdx + 3] = 0;
            }
          }

          localCtx.putImageData(imgData, 0, 0);
          const blob = await new Promise<Blob | null>((resolve) => localCanvas.toBlob(resolve, 'image/png'));
          if (!blob) throw new Error("Failed to export blob during clean parallel execution");

          return {
            ...frame,
            dataUrl: localCanvas.toDataURL('image/png'),
            blob
          };
        }
      );

      const validCleaned = cleaned.filter(Boolean);
      setFrames(validCleaned);
      setIsCleaningProgress(false);
    }
  };

  // ZIP package exporter (multi-tier output directory mapping!)
  const downloadZipPackage = async () => {
    if (frames.length === 0) return;

    const zip = new JSZip();

    if (currentTab === 'translucent' && gameDualExportChecked) {
      // Specialized multi-texture setup
      const finalFolder = zip.folder("final");
      const coreFolder = zip.folder("core");
      const glowFolder = zip.folder("glow");

      for (let idx = 0; idx < frames.length; idx++) {
        const frame = frames[idx];
        const filename = `frame_${idx.toString().padStart(4, '0')}.png`;
        finalFolder?.file(filename, frame.blob);

        if (frame.coreDataUrl) {
          const coreBlob = await fetch(frame.coreDataUrl).then(r => r.blob());
          coreFolder?.file(filename, coreBlob);
        }
        if (frame.glowDataUrl) {
          const glowBlob = await fetch(frame.glowDataUrl).then(r => r.blob());
          glowFolder?.file(filename, glowBlob);
        }
      }
    } else {
      // Default direct ZIP packing
      const spritesFolder = zip.folder("sprites");
      frames.forEach((frame, idx) => {
        const filename = `frame_${idx.toString().padStart(4, '0')}.png`;
        spritesFolder?.file(filename, frame.blob);
      });
    }

    const content = await zip.generateAsync({ type: "blob" });
    const url = URL.createObjectURL(content);
    const link = document.createElement('a');
    link.href = url;
    link.download = `pixel_pro_extract_${Date.now()}.zip`;
    link.click();
    URL.revokeObjectURL(url);
  };

  // Reset project state
  const resetProjectState = () => {
    setVideoFile(null);
    setVideoUrl('');
    setBatchFiles([]);
    setFrames([]);
    setRawFrames([]);
    setQuantizedFrames([]);
    setTrimaps({});
    setProtectMasks({});
    setPreviewIndex(0);
    setIsPreviewing(false);
  };

  // Visual background inspection styling mapping
  const getInspectBackdropClass = () => {
    switch (cleanupBGMock) {
      case 'white': return 'bg-white';
      case 'black': return 'bg-black';
      case 'green': return 'bg-[#00ff00]';
      case 'pink': return 'bg-[#ff00ff]';
      default: return 'checkerboard';
    }
  };

  // Active preview image source calculator
  const getActiveViewUrl = () => {
    if (frames.length === 0) return '';
    if (currentTab === 'translucent') {
      if (activePreviewMode === 'trimap') return currentTrimapDataUrl || frames[previewIndex]?.dataUrl || '';
      if (activePreviewMode === 'core') return currentCoreDataUrl || frames[previewIndex]?.dataUrl || '';
      if (activePreviewMode === 'glow') return currentGlowDataUrl || frames[previewIndex]?.dataUrl || '';
      if (activePreviewMode === 'final') return currentFinalDataUrl || frames[previewIndex]?.dataUrl || '';
      return rawFrames[previewIndex]?.dataUrl || '';
    }
    return frames[previewIndex]?.dataUrl || '';
  };

  return (
    <div 
      className="flex flex-col h-screen bg-slate-50 text-slate-900 font-sans overflow-hidden"
      onDragOver={(e) => { e.preventDefault(); setIsDragging(true); }}
      onDragLeave={(e) => { e.preventDefault(); setIsDragging(false); }}
      onDrop={(e) => {
        e.preventDefault();
        setIsDragging(false);
        const file = e.dataTransfer.files?.[0];
        if (file) {
          if (file.type.startsWith('video/')) loadVideo(file);
          else if (file.type.startsWith('image/')) setBatchFiles(Array.from(e.dataTransfer.files));
        }
      }}
    >
      {/* Drag & Drop Window Mask */}
      <AnimatePresence>
        {isDragging && (
          <motion.div 
            initial={{ opacity: 0 }}
            animate={{ opacity: 1 }}
            exit={{ opacity: 0 }}
            className="absolute inset-0 bg-indigo-600/20 backdrop-blur-sm z-[100] flex items-center justify-center p-12"
          >
            <div className="w-full h-full border-4 border-dashed border-indigo-600 rounded-[40px] flex flex-col items-center justify-center gap-4 bg-white/95 shadow-xl">
              <Upload className="w-16 h-16 text-indigo-600 animate-bounce" />
              <h2 className="text-2xl font-bold text-slate-800">{t('dragPlaceholder')}</h2>
            </div>
          </motion.div>
        )}
      </AnimatePresence>

      {/* Main Top Navbar */}
      <nav className="h-16 border-b border-slate-200 bg-white flex items-center justify-between px-8 shrink-0 shadow-sm z-30">
        <div className="flex items-center gap-3">
          <div className="w-8 h-8 bg-indigo-600 rounded flex items-center justify-center shadow-md">
            <div className="w-4 h-4 bg-white grid grid-cols-2 gap-0.5 p-0.5">
              <div className="bg-indigo-600"></div>
              <div className="bg-indigo-600"></div>
              <div className="bg-indigo-600"></div>
              <div className="bg-indigo-600"></div>
            </div>
          </div>
          <h1 className="text-lg font-bold tracking-tight">{t('title')}</h1>
          <div className="text-[10px] bg-slate-100 font-mono font-bold text-slate-500 px-2 py-0.5 rounded ml-2">
            {t('stableVersion')}
          </div>
        </div>

        {/* Tab selection links */}
        <div className="flex bg-slate-100 p-1 rounded-xl border border-slate-200 max-w-lg">
          <button 
            type="button"
            onClick={() => setCurrentTab('video')}
            className={cn("px-4 py-1.5 rounded-lg text-xs font-bold transition-all flex items-center gap-1.5", currentTab === 'video' ? "bg-white text-indigo-600 shadow" : "text-slate-500 hover:text-slate-800")}
          >
            <Monitor className="w-3.5 h-3.5" />
            {t('videoMode')}
          </button>
          <button 
            type="button"
            onClick={() => setCurrentTab('batch')}
            className={cn("px-4 py-1.5 rounded-lg text-xs font-bold transition-all flex items-center gap-1.5", currentTab === 'batch' ? "bg-white text-indigo-600 shadow" : "text-slate-500 hover:text-slate-800")}
          >
            <Files className="w-3.5 h-3.5" />
            {t('batchImages')}
          </button>
          <button 
            type="button"
            onClick={() => setCurrentTab('translucent')}
            className={cn("px-4 py-1.5 rounded-lg text-xs font-bold transition-all flex items-center gap-1.5", currentTab === 'translucent' ? "bg-white text-indigo-600 shadow" : "text-slate-500 hover:text-slate-800")}
          >
            <Sparkles className="w-3.5 h-3.5" />
            {t('translucentMatting')}
          </button>
          <button 
            type="button"
            onClick={() => setCurrentTab('cleanup')}
            className={cn("px-4 py-1.5 rounded-lg text-xs font-bold transition-all flex items-center gap-1.5", currentTab === 'cleanup' ? "bg-white text-indigo-600 shadow" : "text-slate-500 hover:text-slate-800")}
          >
            <Pipette className="w-3.5 h-3.5" />
            {t('edgeCleanup')}
          </button>
        </div>

        <div className="flex items-center gap-4">
          <button 
            type="button"
            onClick={() => setLang(lang === 'zh' ? 'en' : 'zh')}
            className="p-2 border border-slate-200 rounded-lg hover:bg-slate-50 transition-all flex items-center gap-1.5 text-xs font-bold cursor-pointer"
          >
            <Languages className="w-4 h-4 text-slate-600" />
            {lang === 'zh' ? 'EN' : '中文'}
          </button>
          <button 
            type="button"
            onClick={resetProjectState}
            className="px-4 py-2 bg-indigo-600 text-white rounded-lg text-xs font-bold shadow hover:bg-indigo-700 transition"
          >
            {t('newProject')}
          </button>
        </div>
      </nav>

      {/* Primary Panels workspace */}
      <main className="flex-1 flex overflow-hidden">
        
        {/* Left controlling column dynamically updated per currentTab */}
        <aside className="w-80 bg-white border-r border-slate-200 p-6 flex flex-col gap-6 shrink-0 overflow-y-auto custom-scrollbar shadow-sm">
          
          {/* TAB 1: VIDEO MODE Controls */}
          {currentTab === 'video' && (
            <>
              {/* Step 1 */}
              <section className="bg-slate-50/70 p-4 rounded-xl border border-slate-100 flex flex-col gap-4">
                <header className="flex items-center gap-2 mb-1">
                  <span className="w-5 h-5 rounded-full bg-slate-900 text-white flex items-center justify-center text-[10px] font-bold">1</span>
                  <label className="text-[10px] font-bold text-slate-500 uppercase tracking-wider">{t('step1Title')}</label>
                </header>

                {/* Classic vs AI Toggle */}
                <div className="flex bg-slate-100 p-1 rounded-xl border">
                  <button 
                    type="button"
                    onClick={() => setVideoKeyMethod('classic')}
                    className={cn("flex-1 py-1 rounded-lg text-[10px] font-bold transition", videoKeyMethod === 'classic' ? "bg-white text-indigo-600 shadow" : "text-slate-500")}
                  >
                    {t('classicalKey')}
                  </button>
                  <button 
                    type="button"
                    onClick={() => setVideoKeyMethod('ai')}
                    className={cn("flex-1 py-1 rounded-lg text-[10px] font-bold transition", videoKeyMethod === 'ai' ? "bg-white text-indigo-600 shadow" : "text-slate-500")}
                  >
                    {t('aiKey')}
                  </button>
                </div>

                <div className="p-3 bg-white border border-slate-200 rounded-xl">
                  <div className="flex justify-between items-center mb-2">
                    <span className="text-[10px] font-bold text-slate-500">{t('scaleFactor')}</span>
                    <span className="px-2 py-0.5 bg-indigo-600 text-white text-[10px] rounded font-mono font-bold">{scaleFactor}x</span>
                  </div>
                  <input 
                    type="range" min="1" max="16" step="1"
                    value={scaleFactor} 
                    onChange={(e) => setScaleFactor(parseInt(e.target.value))}
                    className="w-full accent-indigo-600 mb-1"
                  />
                  <div className="text-[9px] text-slate-400 font-medium text-center">
                    {t('outRes')}: {Math.floor(videoDimensions.width / scaleFactor)}×{Math.floor(videoDimensions.height / scaleFactor)}px
                  </div>
                </div>

                {videoKeyMethod === 'classic' && (
                  <>
                    <div className="flex flex-col gap-2">
                      <div className="flex justify-between items-center text-[10px] font-bold text-slate-500">
                        <span>{t('transparencyKey')}</span>
                        <button type="button" onClick={() => setTransparentColor(null)} className="text-indigo-600 text-[10px] hover:underline">
                          {t('disableKey')}
                        </button>
                      </div>
                      <div className="flex items-center gap-2 w-full">
                        <div className="relative w-8 h-8 rounded-lg border border-slate-200 flex items-center justify-center p-0 overflow-hidden bg-slate-50 cursor-pointer hover:border-slate-300">
                          <div className="w-full h-full" style={{ backgroundColor: transparentColor || 'transparent' }} />
                          <input 
                            type="color" 
                            value={transparentColor || '#ffffff'} 
                            onChange={(e) => setTransparentColor(e.target.value)} 
                            className="absolute inset-0 opacity-0 cursor-pointer" 
                          />
                        </div>
                        
                        <div className="flex-1 flex items-center gap-1 bg-slate-50 border border-slate-200 px-2.5 py-1 rounded-lg">
                          <span className="text-[10px] font-mono font-bold text-slate-400">#</span>
                          <input 
                            type="text"
                            placeholder="000000"
                            value={colorLocalInput}
                            onChange={(e) => {
                              const text = e.target.value;
                              setColorLocalInput(text);
                              const clean = text.trim().replace('#', '');
                              if (clean.length === 6 && /^[0-9A-Fa-f]{6}$/.test(clean)) {
                                setTransparentColor('#' + clean.toLowerCase());
                              } else if (clean === '') {
                                setTransparentColor(null);
                              }
                            }}
                            className="w-full text-[10px] text-slate-700 font-mono font-bold bg-transparent outline-none uppercase"
                          />
                        </div>
                      </div>
                    </div>

                    <div className="flex items-center gap-2 px-1">
                      <input 
                        type="checkbox" 
                        id="palette-lock-check"
                        checked={paletteLock} 
                        onChange={(e) => setPaletteLock(e.target.checked)}
                        className="rounded text-indigo-600"
                      />
                      <label htmlFor="palette-lock-check" className="text-[10px] font-semibold text-slate-500 uppercase cursor-pointer">
                        {t('advPaletteLock')}
                      </label>
                    </div>
                  </>
                )}

                <div className="flex justify-between items-center bg-white border border-slate-200 rounded-lg p-2.5">
                  <span className="text-[10px] font-bold text-slate-500">{videoKeyMethod === 'classic' ? t('tolerance') : t('detectionTolerance')}</span>
                  <input type="range" min="0" max="150" value={tolerance} onChange={(e) => setTolerance(parseInt(e.target.value))} className="w-24 accent-indigo-600" />
                  <span className="text-[10px] font-mono font-bold text-indigo-600 w-6 text-right">{tolerance}</span>
                </div>

                {/* Worker Concurrency slider */}
                <div className="p-2.5 bg-white border border-slate-200 rounded-lg flex flex-col gap-1.5">
                  <div className="flex justify-between items-center">
                    <span className="text-[10px] font-bold text-slate-500 uppercase">{t('concurrency')}</span>
                    <span className="px-1.5 py-0.5 bg-indigo-600 font-mono font-bold text-white text-[9px] rounded">{concurrency}</span>
                  </div>
                  <input 
                    type="range" min="1" max="15" step="1"
                    value={concurrency}
                    onChange={(e) => setConcurrency(parseInt(e.target.value))}
                    className="w-full accent-indigo-600"
                  />
                </div>

                <button 
                  type="button"
                  onClick={processVideo}
                  disabled={!videoFile || isProcessing}
                  className="w-full py-3 rounded-xl bg-indigo-600 text-white hover:bg-indigo-700 disabled:bg-slate-100 disabled:text-slate-400 font-bold text-xs uppercase tracking-widest flex items-center justify-center gap-2 transition"
                >
                  {isProcessing ? <><Loader2 className="w-3.5 h-3.5 animate-spin"/> {progress}%</> : <><Zap className="w-3.5 h-3.5" />{t('runExtraction')}</>}
                </button>
              </section>

              {/* Step 2 */}
              <section className={cn("transition-opacity flex flex-col gap-3", frames.length === 0 ? "opacity-30 pointer-events-none" : "opacity-100")}>
                <header className="flex items-center gap-2 mb-1">
                  <span className="w-5 h-5 rounded-full bg-slate-900 text-white flex items-center justify-center text-[10px] font-bold">2</span>
                  <label className="text-[10px] font-bold text-slate-500 uppercase tracking-wider">{t('step2Title')}</label>
                </header>

                <div className="p-4 bg-white border border-slate-200 rounded-xl flex flex-col gap-3 shadow-sm">
                  <span className="text-xs font-bold text-slate-700">{t('mergeColors')}</span>
                  <p className="text-[9px] text-slate-400 leading-relaxed font-semibold">{t('mergeDesc')}</p>

                  <div className="flex justify-between items-center py-1">
                    <span className="text-[9px] font-bold text-slate-500 uppercase">{t('paletteTolerance')}</span>
                    <span className="text-indigo-600 font-mono text-[10px] font-bold">{quantizationTolerance}</span>
                  </div>
                  <input type="range" min="0" max="100" value={quantizationTolerance} onChange={(e) => setQuantizationTolerance(parseInt(e.target.value))} className="w-full accent-indigo-600" />

                  <button 
                    type="button"
                    onClick={consolidateColors}
                    disabled={isQuantizing}
                    className="w-full py-2.5 rounded-lg border border-slate-200 bg-white hover:bg-slate-50 text-slate-700 font-bold text-[10px] uppercase flex items-center justify-center gap-1.5 transition"
                  >
                    {isQuantizing ? <><Loader2 className="w-3 h-3 animate-spin"/> {progress}%</> : t('consolidateBtn')}
                  </button>
                </div>
              </section>

              {/* Step 3 */}
              <section className={cn("transition-opacity flex flex-col gap-3", frames.length === 0 ? "opacity-30 pointer-events-none" : "opacity-100")}>
                <header className="flex items-center gap-2 mb-1">
                  <span className="w-5 h-5 rounded-full bg-slate-900 text-white flex items-center justify-center text-[10px] font-bold">3</span>
                  <label className="text-[10px] font-bold text-slate-500 uppercase tracking-wider">{t('step3Title')}</label>
                </header>

                <div className="p-4 bg-white border border-slate-200 rounded-xl flex flex-col gap-3 shadow-sm">
                  <span className="text-xs font-bold text-slate-700">{t('edgeReinforce')}</span>
                  <p className="text-[9px] text-slate-400 leading-relaxed font-semibold">{t('edgeReinforceDesc')}</p>

                  <div className="flex flex-col gap-1.5">
                    <span className="text-[9px] font-bold text-slate-500 uppercase">{t('edgeColor')}</span>
                    <div className="relative h-9 w-full rounded-lg border border-slate-200 bg-slate-50 p-1.5 flex items-center gap-2">
                      <div className="w-5 h-5 rounded border" style={{ backgroundColor: outlineColor }} />
                      <span className="text-[10px] font-mono font-bold text-slate-500">{outlineColor}</span>
                      <input type="color" value={outlineColor} onChange={(e) => setOutlineColor(e.target.value)} className="absolute inset-0 opacity-0 cursor-pointer" />
                    </div>
                  </div>

                  <div className="flex justify-between items-center">
                    <span className="text-[9px] font-bold text-slate-500 uppercase">{t('detectionTolerance')}</span>
                    <span className="text-emerald-600 font-mono text-[10px] font-bold">{repairTolerance}</span>
                  </div>
                  <input type="range" min="10" max="180" value={repairTolerance} onChange={(e) => setRepairTolerance(parseInt(e.target.value))} className="w-full accent-emerald-500" />

                  <button 
                    type="button"
                    onClick={repairExtractedFrames}
                    disabled={isRepairing}
                    className="w-full py-2.5 rounded-lg bg-emerald-600 text-white hover:bg-emerald-700 font-bold text-[10px] uppercase flex items-center justify-center gap-1.5 transition shadow"
                  >
                    {isRepairing ? <><Loader2 className="w-3 h-3 animate-spin"/> {progress}%</> : t('runRepairBtn')}
                  </button>
                </div>
              </section>
            </>
          )}

          {/* TAB 2: BATCH IMAGES Controls */}
          {currentTab === 'batch' && (
            <div className="flex flex-col gap-5">
              <h3 className="text-sm font-bold text-slate-800 uppercase tracking-widest">{t('batchTitle')}</h3>

              <div className="p-4 border-2 border-dashed border-slate-200 rounded-2xl flex flex-col items-center gap-2 hover:bg-slate-50 transition cursor-pointer" onClick={() => document.getElementById('batch-upload-field')?.click()}>
                <Upload className="w-8 h-8 text-neutral-400" />
                <span className="text-[10px] font-bold text-indigo-600 uppercase">{t('selectFiles')}</span>
                <input id="batch-upload-field" type="file" multiple accept="image/*" className="hidden" onChange={handleBatchImageUpload} />
              </div>

              {batchFiles.length > 0 && (
                <div className="flex items-center gap-2 bg-indigo-50 border border-indigo-100 p-2 text-indigo-700 rounded-xl text-[10px] font-bold">
                  {t('uploadedCount').replace('{count}', String(batchFiles.length))}
                </div>
              )}

              {/* Classic vs AI Toggle */}
              <div className="flex bg-slate-100 p-1 rounded-xl border">
                <button 
                  type="button"
                  onClick={() => setBatchKeyMethod('classic')}
                  className={cn("flex-1 py-1.5 rounded-lg text-xs font-bold transition", batchKeyMethod === 'classic' ? "bg-white text-indigo-600 shadow" : "text-slate-500")}
                >
                  {t('classicalKey')}
                </button>
                <button 
                  type="button"
                  onClick={() => setBatchKeyMethod('ai')}
                  className={cn("flex-1 py-1.5 rounded-lg text-xs font-bold transition", batchKeyMethod === 'ai' ? "bg-white text-indigo-600 shadow" : "text-slate-500")}
                >
                  {t('aiKey')}
                </button>
              </div>

              {/* Scaling inside Batch */}
              <div className="p-3 bg-white border rounded-xl shadow-sm">
                <div className="flex justify-between items-center mb-1.5">
                  <span className="text-[10px] font-bold text-slate-500">{t('scaleFactor')}</span>
                  <span className="text-indigo-600 font-mono text-[10px] font-bold">{scaleFactor}x</span>
                </div>
                <input type="range" min="1" max="16" value={scaleFactor} onChange={(e) => setScaleFactor(parseInt(e.target.value))} className="w-full accent-indigo-600" />
                <div className="text-[8px] text-slate-400 font-semibold text-center mt-1">If files are raw pixels, set to 1x</div>
              </div>

              {batchKeyMethod === 'classic' && (
                <div className="flex flex-col gap-3">
                  <div className="flex items-center gap-2 w-full">
                    <div className="relative w-8 h-8 rounded-lg border border-slate-200 flex items-center justify-center p-0 overflow-hidden bg-slate-50 cursor-pointer hover:border-slate-300">
                      <div className="w-full h-full" style={{ backgroundColor: transparentColor || 'transparent' }} />
                      <input 
                        type="color" 
                        value={transparentColor || '#ffffff'} 
                        onChange={(e) => setTransparentColor(e.target.value)} 
                        className="absolute inset-0 opacity-0 cursor-pointer" 
                      />
                    </div>
                    
                    <div className="flex-1 flex items-center gap-1 bg-slate-50 border border-slate-200 px-2.5 py-1 rounded-lg">
                      <span className="text-[10px] font-mono font-bold text-slate-400">#</span>
                      <input 
                        type="text"
                        placeholder="000000"
                        value={colorLocalInput}
                        onChange={(e) => {
                          const text = e.target.value;
                          setColorLocalInput(text);
                          const clean = text.trim().replace('#', '');
                          if (clean.length === 6 && /^[0-9A-Fa-f]{6}$/.test(clean)) {
                            setTransparentColor('#' + clean.toLowerCase());
                          } else if (clean === '') {
                            setTransparentColor(null);
                          }
                        }}
                        className="w-full text-[10px] text-slate-700 font-mono font-bold bg-transparent outline-none uppercase"
                      />
                    </div>
                  </div>
                  <div className="flex justify-between items-center bg-white border rounded-lg p-2.5">
                    <span className="text-[10px] font-bold text-slate-500">{t('tolerance')}</span>
                    <input type="range" min="0" max="150" value={tolerance} onChange={(e) => setTolerance(parseInt(e.target.value))} className="w-24 accent-indigo-600" />
                    <span className="text-[10px] font-mono font-bold text-indigo-600 w-6 text-right">{tolerance}</span>
                  </div>
                </div>
              )}

              {/* Worker Concurrency slider */}
              <div className="p-3 bg-white border rounded-xl shadow-sm flex flex-col gap-1.5">
                <div className="flex justify-between items-center">
                  <span className="text-[10px] font-bold text-slate-500 uppercase">{t('concurrency')}</span>
                  <span className="px-1.5 py-0.5 bg-indigo-600 font-mono font-bold text-white text-[9px] rounded">{concurrency}</span>
                </div>
                <input 
                  type="range" min="1" max="15" step="1"
                  value={concurrency}
                  onChange={(e) => setConcurrency(parseInt(e.target.value))}
                  className="w-full accent-indigo-600"
                />
              </div>

              <button 
                type="button"
                onClick={executeBatchProcess}
                disabled={batchFiles.length === 0 || isBatchRunning}
                className="w-full py-3.5 rounded-xl bg-indigo-600 text-white font-bold text-xs uppercase tracking-widest hover:bg-indigo-700 shadow-md transition disabled:bg-slate-100 disabled:text-slate-400 text-center flex items-center justify-center gap-2"
              >
                {isBatchRunning ? <><Loader2 className="w-3.5 h-3.5 animate-spin" />{progress}%</> : t('runBatchExtraction')}
              </button>

              {frames.length > 0 && (
                <>
                  <div className="border-t border-slate-100 my-2" />
                  
                  {/* Step 2: Merge Colors */}
                  <section className="flex flex-col gap-3">
                    <header className="flex items-center gap-2 mb-1">
                      <span className="w-5 h-5 rounded-full bg-slate-900 text-white flex items-center justify-center text-[10px] font-bold">2</span>
                      <label className="text-[10px] font-bold text-slate-500 uppercase tracking-wider">{t('step2Title')}</label>
                    </header>

                    <div className="p-4 bg-white border border-slate-200 rounded-xl flex flex-col gap-3 shadow-sm">
                      <span className="text-xs font-bold text-slate-700">{t('mergeColors')}</span>
                      <p className="text-[9px] text-slate-400 leading-relaxed font-semibold">{t('mergeDesc')}</p>

                      <div className="flex justify-between items-center py-1">
                        <span className="text-[9px] font-bold text-slate-500 uppercase">{t('paletteTolerance')}</span>
                        <span className="text-indigo-600 font-mono text-[10px] font-bold">{quantizationTolerance}</span>
                      </div>
                      <input type="range" min="0" max="100" value={quantizationTolerance} onChange={(e) => setQuantizationTolerance(parseInt(e.target.value))} className="w-full accent-indigo-600" />

                      <button 
                        type="button"
                        onClick={consolidateColors}
                        disabled={isQuantizing}
                        className="w-full py-2.5 rounded-lg border border-slate-200 bg-white hover:bg-slate-50 text-slate-700 font-bold text-[10px] uppercase flex items-center justify-center gap-1.5 transition"
                      >
                        {isQuantizing ? <><Loader2 className="w-3 h-3 animate-spin"/> {progress}%</> : t('consolidateBtn')}
                      </button>
                    </div>
                  </section>

                  {/* Step 3: Edge Reinforce */}
                  <section className="flex flex-col gap-3">
                    <header className="flex items-center gap-2 mb-1">
                      <span className="w-5 h-5 rounded-full bg-slate-900 text-white flex items-center justify-center text-[10px] font-bold">3</span>
                      <label className="text-[10px] font-bold text-slate-500 uppercase tracking-wider">{t('step3Title')}</label>
                    </header>

                    <div className="p-4 bg-white border border-slate-200 rounded-xl flex flex-col gap-3 shadow-sm">
                      <span className="text-xs font-bold text-slate-700">{t('edgeReinforce')}</span>
                      <p className="text-[9px] text-slate-400 leading-relaxed font-semibold">{t('edgeReinforceDesc')}</p>

                      <div className="flex flex-col gap-1.5">
                        <span className="text-[9px] font-bold text-slate-500 uppercase">{t('edgeColor')}</span>
                        <div className="relative h-9 w-full rounded-lg border border-slate-200 bg-slate-50 p-1.5 flex items-center gap-2">
                          <div className="w-5 h-5 rounded border" style={{ backgroundColor: outlineColor }} />
                          <span className="text-[10px] font-mono font-bold text-slate-500">{outlineColor}</span>
                          <input type="color" value={outlineColor} onChange={(e) => setOutlineColor(e.target.value)} className="absolute inset-0 opacity-0 cursor-pointer" />
                        </div>
                      </div>

                      <div className="flex justify-between items-center">
                        <span className="text-[9px] font-bold text-slate-500 uppercase">{t('detectionTolerance')}</span>
                        <span className="text-emerald-600 font-mono text-[10px] font-bold">{repairTolerance}</span>
                      </div>
                      <input type="range" min="10" max="180" value={repairTolerance} onChange={(e) => setRepairTolerance(parseInt(e.target.value))} className="w-full accent-emerald-500" />

                      <button 
                        type="button"
                        onClick={repairExtractedFrames}
                        disabled={isRepairing}
                        className="w-full py-2.5 rounded-lg bg-emerald-600 text-white hover:bg-emerald-700 font-bold text-[10px] uppercase flex items-center justify-center gap-1.5 transition shadow"
                      >
                        {isRepairing ? <><Loader2 className="w-3 h-3 animate-spin"/> {progress}%</> : t('runRepairBtn')}
                      </button>
                    </div>
                  </section>
                </>
              )}
            </div>
          )}

          {/* TAB 3: TRANSLUCENT MATTING Controls */}
          {currentTab === 'translucent' && (
            <div className="flex flex-col gap-5">
              <h3 className="text-sm font-bold text-slate-800 uppercase tracking-widest">{t('translucentTitle')}</h3>

              {frames.length === 0 ? (
                // Quick Media Import Sidebar Panel
                <div className="p-4 bg-slate-50 border border-slate-200 rounded-xl flex flex-col gap-3 shadow-sm">
                  <span className="text-[10px] font-bold text-slate-500 uppercase tracking-wider">{lang === 'zh' ? '在此导入媒体' : 'Import Media Here'}</span>
                  <p className="text-[10px] text-slate-400 font-medium leading-relaxed">
                    {lang === 'zh' 
                      ? '半透明抠图支持视频导入、单张或多张图片以及整个文件夹。' 
                      : 'Translucent matting supports videos, folder selections, and standard sprite image assets.'}
                  </p>
                  
                  <div className="flex flex-col gap-2 mt-1">
                    <button
                      type="button"
                      onClick={() => document.getElementById('initial-upload-trigger')?.click()}
                      className="w-full py-2 bg-indigo-600 text-white rounded-lg text-xs font-bold hover:bg-indigo-700 transition flex items-center justify-center gap-1.5 shadow"
                    >
                      <Upload className="w-3.5 h-3.5" />
                      {lang === 'zh' ? '导入源素材' : 'Import Media'}
                    </button>
                    <button
                      type="button"
                      onClick={() => document.getElementById('folder-upload-trigger')?.click()}
                      className="w-full py-2 bg-white border border-slate-200 text-slate-700 rounded-lg text-xs font-bold hover:bg-slate-50 transition flex items-center justify-center gap-1.5 shadow-sm"
                    >
                      <Folder className="w-3.5 h-3.5 text-indigo-600" />
                      {t('selectFolder')}
                    </button>
                  </div>
                </div>
              ) : (
                <>
                  <p className="text-[10px] text-slate-400 leading-relaxed font-semibold">{t('translucentStepDesc')}</p>

                  {/* Brush Stencil */}
                  <div className="p-4 bg-slate-50 border border-slate-100 rounded-xl flex flex-col gap-3">
                    <span className="text-[9px] font-bold text-slate-500 uppercase tracking-wider">{t('brushTitle')}</span>
                    <div className="flex flex-col gap-2">
                      <button 
                        type="button"
                        onClick={() => setBrushMode('fg')}
                        className={cn("py-2 rounded-lg text-xs font-bold text-left px-3 flex items-center justify-between border transition", brushMode === 'fg' ? "bg-green-500 text-white border-green-600 shadow" : "bg-white text-slate-700 border-slate-200")}
                      >
                        <span>{t('sureFG')}</span>
                        <span className="w-2.5 h-2.5 rounded-full bg-white border border-green-700" />
                      </button>
                      <button 
                        type="button"
                        onClick={() => setBrushMode('bg')}
                        className={cn("py-2 rounded-lg text-xs font-bold text-left px-3 flex items-center justify-between border transition", brushMode === 'bg' ? "bg-red-500 text-white border-red-650 shadow" : "bg-white text-slate-700 border-slate-200")}
                      >
                        <span>{t('sureBG')}</span>
                        <span className="w-2.5 h-2.5 rounded-full bg-white border border-red-700" />
                      </button>
                      <button 
                        type="button"
                        onClick={() => setBrushMode('unknown')}
                        className={cn("py-2 rounded-lg text-xs font-bold text-left px-3 flex items-center justify-between border transition", brushMode === 'unknown' ? "bg-blue-500 text-white border-blue-600 shadow" : "bg-white text-slate-700 border-slate-200")}
                      >
                        <span>{t('unknown')}</span>
                        <span className="w-2.5 h-2.5 rounded-full bg-white border border-blue-700" />
                      </button>
                    </div>

                    <div className="flex justify-between items-center py-1 mt-1">
                      <span className="text-[9px] font-bold text-slate-500">{t('brushDiameter')}</span>
                      <span className="text-indigo-600 font-mono text-[10px] font-bold">{trimapBrushSize}px</span>
                    </div>
                    <input type="range" min="1" max="40" value={trimapBrushSize} onChange={(e) => setTrimapBrushSize(parseInt(e.target.value))} className="w-full accent-indigo-600" />

                    <div className="grid grid-cols-2 gap-2 mt-2">
                      <button type="button" onClick={autoBuildActiveTrimap} className="py-2 rounded-lg bg-indigo-50 border border-indigo-100 hover:bg-indigo-100 text-indigo-700 font-bold text-[9px] uppercase tracking-wider transition">
                        {t('autoTrimap')}
                      </button>
                      <button 
                        type="button"
                        onClick={() => {
                          setTrimaps(prev => ({ ...prev, [previewIndex]: new Uint8Array(0) }));
                        }}
                        className="py-2 rounded-lg bg-white border border-slate-200 hover:bg-slate-50 text-slate-500 font-bold text-[9px] uppercase tracking-wider transition"
                      >
                        {t('clearTrimap')}
                      </button>
                    </div>
                  </div>

                  {/* Sliders */}
                  <div className="p-3 bg-white border rounded-xl shadow-sm flex flex-col gap-4">
                    {/* Pure FX / Glow mode switch */}
                    <div className="flex flex-col gap-1.5 p-2.5 bg-indigo-50/60 border border-indigo-100/50 rounded-lg">
                      <div className="flex items-center justify-between">
                        <label htmlFor="pure-glow-toggle" className="text-[10px] font-bold text-[#4f46e5] cursor-pointer uppercase tracking-wider">
                          {t('pureGlowModeLabel')}
                        </label>
                        <input 
                          type="checkbox" 
                          id="pure-glow-toggle" 
                          checked={pureGlowMode} 
                          onChange={(e) => setPureGlowMode(e.target.checked)} 
                          className="w-3.5 h-3.5 text-indigo-600 rounded cursor-pointer accent-indigo-600"
                        />
                      </div>
                      <p className="text-[9px] text-[#475569] leading-relaxed font-semibold">
                        {t('pureGlowModeDesc')}
                      </p>
                    </div>

                    <div className="flex flex-col gap-1.5" style={{ opacity: pureGlowMode ? 0.45 : 1.0, pointerEvents: pureGlowMode ? 'none' : 'auto' }}>
                      <div className="flex justify-between items-center font-bold">
                        <span className="text-[10px] text-slate-500 uppercase">{t('coreTolerance')}</span>
                        <span className="text-slate-700 font-mono text-[11px]">{coreTolerance}</span>
                      </div>
                      <input type="range" min="0" max="120" value={coreTolerance} onChange={(e) => setCoreTolerance(parseInt(e.target.value))} className="w-full" disabled={pureGlowMode} />
                    </div>

                    <div className="flex flex-col gap-1.5">
                      <div className="flex justify-between items-center font-bold">
                        <span className="text-[10px] text-slate-500 uppercase">{t('glowRadius')}</span>
                        <span className="text-slate-700 font-mono text-[11px]">{glowRadiusVal}</span>
                      </div>
                      <input type="range" min="1" max="25" value={glowRadiusVal} onChange={(e) => setGlowRadiusVal(parseInt(e.target.value))} className="w-full" />
                    </div>
                  </div>

                  {/* Synthesizers */}
                  <div className="flex flex-col gap-2">
                    <span className="text-[9px] font-bold text-slate-500 uppercase">{t('blendMode')}</span>
                    <div className="grid grid-cols-3 gap-2 bg-slate-100 p-1 rounded-xl">
                      <button 
                        type="button"
                        onClick={() => setGlowBlendMode('normal')}
                        className={cn("py-1.5 rounded-lg text-[9px] font-bold transition", glowBlendMode === 'normal' ? "bg-white text-slate-800 shadow" : "text-slate-500")}
                      >
                        {t('normalBlend')}
                      </button>
                      <button 
                        type="button"
                        onClick={() => setGlowBlendMode('screen')}
                        className={cn("py-1.5 rounded-lg text-[9px] font-bold transition", glowBlendMode === 'screen' ? "bg-white text-slate-800 shadow" : "text-slate-500")}
                      >
                        {t('screenBlend')}
                      </button>
                      <button 
                        type="button"
                        onClick={() => setGlowBlendMode('add')}
                        className={cn("py-1.5 rounded-lg text-[9px] font-bold transition", glowBlendMode === 'add' ? "bg-white text-slate-800 shadow" : "text-slate-500")}
                      >
                        {t('addBlend')}
                      </button>
                    </div>
                  </div>

                  {/* Game optimization */}
                  <div className="flex items-center gap-2 px-1">
                    <input 
                      type="checkbox" 
                      id="game-dual-tex" 
                      checked={gameDualExportChecked} 
                      onChange={(e) => setGameDualExportChecked(e.target.checked)} 
                      className="rounded text-indigo-600"
                    />
                    <label htmlFor="game-dual-tex" className="text-[10px] font-bold text-slate-500 hover:text-slate-800 cursor-pointer">
                      {t('gameDualExport')}
                    </label>
                  </div>

                  <button 
                    type="button"
                    onClick={executeTranslucentMattingSeq}
                    disabled={isMattingSequence}
                    className="w-full py-4 bg-indigo-600 hover:bg-indigo-700 text-white rounded-xl text-xs font-bold uppercase tracking-widest shadow-md transition flex items-center justify-center gap-2"
                  >
                    {isMattingSequence ? <><Loader2 className="w-4 h-4 animate-spin"/> {progress}%</> : <><Sparkles className="w-4 h-4 text-amber-300"/>{t('runTransMatting')}</>}
                  </button>
                </>
              )}
            </div>
          )}

          {/* TAB 4: EDGE CLEANUP Controls */}
          {currentTab === 'cleanup' && (
            <div className="flex flex-col gap-5">
              <h3 className="text-sm font-bold text-slate-800 uppercase tracking-widest">{t('cleanupTitle')}</h3>

              {frames.length === 0 ? (
                // Quick Media Import Sidebar Panel for Cleanup
                <div className="p-4 bg-slate-50 border border-slate-200 rounded-xl flex flex-col gap-3 shadow-sm">
                  <span className="text-[10px] font-bold text-slate-500 uppercase tracking-wider">{lang === 'zh' ? '在此导入媒体' : 'Import Media Here'}</span>
                  <p className="text-[10px] text-slate-400 font-medium leading-relaxed">
                    {lang === 'zh' 
                      ? '边缘清理支持视频、单张或多张图片以及整个文件夹。' 
                      : 'Edge cleanup handles frame clearance of any single image, folder of assets, or video.'}
                  </p>
                  
                  <div className="flex flex-col gap-2 mt-1">
                    <button
                      type="button"
                      onClick={() => document.getElementById('initial-upload-trigger')?.click()}
                      className="w-full py-2 bg-indigo-600 text-white rounded-lg text-xs font-bold hover:bg-indigo-700 transition flex items-center justify-center gap-1.5 shadow"
                    >
                      <Upload className="w-3.5 h-3.5" />
                      {lang === 'zh' ? '导入源素材' : 'Import Media'}
                    </button>
                    <button
                      type="button"
                      onClick={() => document.getElementById('folder-upload-trigger')?.click()}
                      className="w-full py-2 bg-white border border-slate-200 text-slate-700 rounded-lg text-xs font-bold hover:bg-slate-50 transition flex items-center justify-center gap-1.5 shadow-sm"
                    >
                      <Folder className="w-3.5 h-3.5 text-indigo-600" />
                      {t('selectFolder')}
                    </button>
                  </div>
                </div>
              ) : (
                <>
                  <p className="text-[10px] text-slate-400 font-semibold leading-relaxed">{t('cleanupDesc')}</p>

                  {/* Backdrop checker */}
                  <div className="flex flex-col gap-1.5">
                    <span className="text-[9px] font-bold text-slate-500 uppercase">{t('canvasBG')}</span>
                    <div className="grid grid-cols-5 gap-1.5">
                      <button 
                        type="button"
                        title={t('transparentCheck')}
                        onClick={() => setCleanupBGMock('transparent')}
                        className={cn("aspect-square rounded border-2 checkerboard", cleanupBGMock === 'transparent' ? 'border-indigo-600 scale-105 shadow' : 'border-slate-200')}
                      />
                      <button 
                        type="button"
                        title={t('whiteBG')}
                        onClick={() => setCleanupBGMock('white')}
                        className={cn("aspect-square rounded border-2 bg-white", cleanupBGMock === 'white' ? 'border-slate-800 scale-105 shadow' : 'border-slate-200')}
                      />
                      <button 
                        type="button"
                        title={t('blackBG')}
                        onClick={() => setCleanupBGMock('black')}
                        className={cn("aspect-square rounded border-2 bg-black", cleanupBGMock === 'black' ? 'border-slate-800 scale-105 shadow' : 'border-slate-200')}
                      />
                      <button 
                        type="button"
                        title={t('greenBG')}
                        onClick={() => setCleanupBGMock('green')}
                        className={cn("aspect-square rounded border-2 bg-[#00ff00]", cleanupBGMock === 'green' ? 'border-slate-800 scale-105 shadow' : 'border-slate-200')}
                      />
                      <button 
                        type="button"
                        title={t('pinkBG')}
                        onClick={() => setCleanupBGMock('pink')}
                        className={cn("aspect-square rounded border-2 bg-[#ff00ff]", cleanupBGMock === 'pink' ? 'border-slate-800 scale-105 shadow' : 'border-slate-200')}
                      />
                    </div>
                  </div>

                  {/* Stain Remover */}
                  <div className="p-4 bg-slate-50 border border-slate-100 rounded-xl flex flex-col gap-3">
                    <span className="text-[9px] font-bold text-slate-500 uppercase tracking-wider">{t('pickCleanColor')}</span>
                    
                    <div className="flex gap-2">
                      <div className="relative flex-1 h-10 rounded-xl border bg-white p-2 flex items-center gap-2">
                        <div className="w-5 h-5 rounded border shadow-inner" style={{ backgroundColor: stainColor }} />
                        <span className="text-[10px] font-mono font-bold text-slate-600 uppercase">{stainColor}</span>
                        <input type="color" value={stainColor} onChange={(e) => setStainColor(e.target.value)} className="absolute inset-0 opacity-0 cursor-pointer" />
                      </div>
                      <button 
                        type="button"
                        onClick={() => setStainPipetteActive(!stainPipetteActive)}
                        className={cn("p-2 rounded-xl border flex items-center justify-center transition", stainPipetteActive ? "bg-indigo-600 text-white border-indigo-600" : "bg-white text-slate-600 border-slate-200 hover:bg-slate-50")}
                        title="Pipette tool"
                      >
                        <Pipette className="w-5 h-5" />
                      </button>
                    </div>
                    {stainPipetteActive && (
                      <p className="text-[8px] text-indigo-600 leading-normal font-semibold italic">{t('pipetteDesc')}</p>
                    )}

                    <div className="flex justify-between items-center py-1 mt-1">
                      <span className="text-[9px] font-bold text-slate-500">{t('cleanupStrength')}</span>
                      <span className="text-indigo-600 font-mono text-[10px] font-bold">{cleanupStrength}</span>
                    </div>
                    <input type="range" min="1" max="100" value={cleanupStrength} onChange={(e) => setCleanupStrength(parseInt(e.target.value))} className="w-full accent-indigo-600" />
                    
                    <div className="grid grid-cols-2 gap-2 mt-1">
                      <button 
                        type="button"
                        onClick={() => runStainCleaner(false)}
                        className="py-2 rounded-lg bg-indigo-600 hover:bg-indigo-700 text-white font-bold text-[9px] uppercase tracking-wider transition"
                      >
                        {t('cleanNoiseBtn')}
                      </button>
                      <button 
                        type="button"
                        onClick={() => runStainCleaner(true)}
                        className="py-2 rounded-lg bg-indigo-50 border border-indigo-150 text-indigo-700 hover:bg-indigo-100 font-bold text-[9px] uppercase tracking-wider transition font-mono"
                      >
                        CLEAN ALL FRAMES
                      </button>
                    </div>

                    <div className="grid grid-cols-2 gap-2 mt-2 border-t border-slate-200/50 pt-2">
                      <button 
                        type="button"
                        onClick={() => {
                          if (cleanupHistory.length > 0) {
                            const prev = cleanupHistory[cleanupHistory.length - 1];
                            setFrames(prev);
                            setCleanupHistory(cleanupHistory.slice(0, -1));
                          }
                        }}
                        disabled={cleanupHistory.length === 0}
                        className={cn("py-2 rounded-lg font-bold text-[9px] uppercase tracking-wider transition flex items-center justify-center gap-1.5", 
                          cleanupHistory.length > 0 
                            ? "bg-amber-500 hover:bg-amber-600 text-white shadow-sm cursor-pointer" 
                            : "bg-slate-100 text-slate-400 cursor-not-allowed"
                        )}
                      >
                        <Undo className="w-3 h-3" />
                        {t('undoCleanupBtn')}
                      </button>
                      <button 
                        type="button"
                        onClick={() => {
                          if (initialCleanupState.length > 0) {
                            setFrames([...initialCleanupState]);
                            setCleanupHistory([]);
                          }
                        }}
                        disabled={initialCleanupState.length === 0}
                        className={cn("py-2 rounded-lg font-bold text-[9px] uppercase tracking-wider transition flex items-center justify-center gap-1.5",
                          initialCleanupState.length > 0 
                            ? "bg-rose-500 hover:bg-rose-600 text-white shadow-sm cursor-pointer" 
                            : "bg-slate-100 text-slate-400 cursor-not-allowed"
                        )}
                      >
                        <RotateCcw className="w-3 h-3" />
                        {t('revertCleanupBtn')}
                      </button>
                    </div>
                  </div>

                  {/* Protected Mask Paint */}
                  <div className="p-4 bg-white border border-slate-100 rounded-xl flex flex-col gap-3 shadow-inner">
                    <div className="flex flex-col gap-0.5">
                      <span className="text-xs font-bold text-slate-700">{t('protectBrushTitle')}</span>
                      <p className="text-[9px] text-slate-400 font-semibold leading-relaxed">{t('protectBrushDesc')}</p>
                    </div>

                    <div className="flex gap-2">
                      <button 
                        type="button"
                        onClick={() => setCleanupProtectActive(!cleanupProtectActive)}
                        className={cn("flex-1 py-2 rounded-lg text-[10px] font-bold transition flex items-center justify-center gap-1.5 border", cleanupProtectActive ? "bg-red-500 text-white border-red-600 shadow" : "bg-white text-slate-700 border-slate-200")}
                      >
                        <Brush className="w-3.5 h-3.5" />
                        {t('addProtectMask')}
                      </button>
                      <button 
                        type="button"
                        onClick={() => {
                          setProtectMasks(prev => ({ ...prev, [previewIndex]: new Uint8Array(0) }));
                        }}
                        className="flex-1 py-2 rounded-lg bg-white hover:bg-slate-50 text-slate-500 border border-slate-200 font-bold text-[10px] transition"
                      >
                        {t('clearProtectMask')}
                      </button>
                    </div>

                    <div className="flex justify-between items-center py-0.5">
                      <span className="text-[9px] font-bold text-slate-500">RADIUS</span>
                      <span className="text-slate-700 font-mono text-[10px] font-bold">{cleanupBrushSize}px</span>
                    </div>
                    <input type="range" min="1" max="40" value={cleanupBrushSize} onChange={(e) => setCleanupBrushSize(parseInt(e.target.value))} className="w-full accent-indigo-600" />
                  </div>

                  {/* Commit changes */}
                  <button 
                    type="button"
                    onClick={() => {
                      setRawFrames([...frames]);
                      setQuantizedFrames([]);
                      setInitialCleanupState([...frames]);
                      setCleanupHistory([]);
                    }}
                    className="w-full py-3.5 rounded-xl border border-dashed border-emerald-500 bg-emerald-50/50 text-emerald-700 hover:bg-emerald-50 hover:scale-[1.01] transition-all font-bold text-[10px] uppercase tracking-wider flex items-center justify-center gap-1.5 animate-pulse"
                  >
                    <Check className="w-4 h-4" />
                    {t('updateCommitBtn')}
                  </button>
                </>
              )}
            </div>
          )}

          {/* Action trigger ZIP Package */}
          <section className="mt-auto pt-6 border-t border-slate-100 shrink-0">
            {frames.length > 0 && (
              <button 
                type="button"
                onClick={downloadZipPackage} 
                className="w-full py-4 bg-slate-900 border border-slate-950 text-white rounded-xl font-bold text-xs flex items-center justify-center gap-3 shadow hover:bg-slate-800 transition active:scale-98 uppercase tracking-widest"
              >
                <Download className="w-4 h-4" />
                {t('packageProject')}
              </button>
            )}
          </section>
        </aside>

        {/* Content central workspace layout */}
        <section className="flex-1 flex flex-col bg-slate-50 relative min-w-0">
          
          <header className="h-12 bg-white border-b border-slate-200 px-6 flex items-center justify-between shrink-0 z-20 shadow-sm">
            <div className="flex gap-6 h-full font-mono">
              <button 
                type="button"
                onClick={() => setIsPreviewing(!isPreviewing)}
                disabled={frames.length === 0}
                className={cn(
                  "text-xs font-bold h-full flex items-center px-1 transition border-b-2 uppercase tracking-widest disabled:opacity-30 flex gap-1.5",
                  isPreviewing ? "text-indigo-600 border-indigo-600" : "text-slate-400 border-transparent hover:text-slate-600"
                )}
              >
                {isPreviewing ? <Pause className="w-3.5 h-3.5 fill-current" /> : <Play className="w-3.5 h-3.5 fill-current" />}
                {isPreviewing ? "HALT INDEX" : "PLAY SEQUENCE"}
              </button>
            </div>

            {/* Translucent matte preview channels */}
            {currentTab === 'translucent' && frames.length > 0 && (
              <div className="flex bg-slate-100 p-1 rounded-lg border border-slate-200 gap-1">
                {(['source', 'trimap', 'core', 'glow', 'final'] as PreviewMode[]).map((mode) => (
                  <button 
                    key={mode}
                    type="button"
                    onClick={() => setActivePreviewMode(mode)}
                    className={cn("px-2.5 py-1 rounded text-[9px] font-bold uppercase transition", activePreviewMode === mode ? "bg-white text-slate-800 shadow" : "text-slate-500 hover:text-slate-800")}
                  >
                    {mode}
                  </button>
                ))}
              </div>
            )}

            <div className="text-[10px] font-bold text-slate-400 font-mono tracking-widest uppercase">
              {frames.length > 0 ? t('frameCount').replace('{count}', String(frames.length)) : t('idleState')}
            </div>
          </header>

          <div className="flex-1 overflow-y-auto p-8 custom-scrollbar">
            {frames.length === 0 && !videoFile && batchFiles.length === 0 ? (
              
              /* Pristine Upload Box Area */
              <div className="h-full flex flex-col items-center justify-center gap-6">
                <div 
                  className="w-24 h-24 rounded-3xl bg-white shadow-xl shadow-slate-200 flex items-center justify-center group cursor-pointer border border-slate-100 hover:scale-105 transition-transform" 
                  onClick={() => document.getElementById('initial-upload-trigger')?.click()}
                >
                  <Upload className="w-10 h-10 text-indigo-600" />
                </div>
                <div className="text-center">
                  <h3 className="text-lg font-bold text-slate-800 mb-1 tracking-tight">{t('importTitle')}</h3>
                  <p className="text-xs text-slate-400 font-semibold">{t('dragPlaceholder')}</p>
                </div>
                <input id="initial-upload-trigger" type="file" className="hidden" accept="video/*,image/*" multiple onChange={(e) => {
                  const first = e.target.files?.[0];
                  if (first) {
                    if (first.type.startsWith('video/')) loadVideo(first);
                    else {
                      setBatchFiles(Array.from(e.target.files || []));
                      setCurrentTab('batch');
                    }
                  }
                }} />
              </div>

            ) : (
              
              /* Active working area canvas previewer */
              <div className="flex flex-col gap-6 max-w-4xl mx-auto h-full">
                
                <div className="bg-white rounded-3xl border border-slate-200 p-3 shadow-xl relative overflow-hidden shrink-0 flex items-center justify-center min-h-[420px]">
                  
                  {/* Backdrop inspect color wrapper */}
                  <div className={cn("w-full h-full rounded-2xl overflow-hidden flex items-center justify-center relative", getInspectBackdropClass())}>
                    
                    {/* Raw Video playback (Only under raw sequence video mode tab) */}
                    {currentTab === 'video' && videoFile && (
                      <video 
                        ref={videoRef}
                        src={videoUrl}
                        className={cn(
                          (isProcessing || frames.length > 0)
                            ? "absolute top-0 left-0 w-1 h-1 opacity-0 pointer-events-none" 
                            : "max-w-full rounded-lg"
                        )}
                        style={{
                          width: '800px',
                          maxWidth: '100%',
                          height: 'auto',
                          aspectRatio: videoDimensions.width && videoDimensions.height ? `${videoDimensions.width} / ${videoDimensions.height}` : '16/9',
                          objectFit: 'contain'
                        }}
                        onLoadedMetadata={onVideoLoaded}
                        muted
                        loop
                      />
                    )}

                    {/* Active Canvas / Image elements */}
                    {frames.length > 0 && (
                      <div 
                        className="relative flex items-center justify-center max-w-full"
                        style={{
                          width: '800px',
                          maxWidth: '100%',
                          aspectRatio: videoDimensions.width && videoDimensions.height ? `${videoDimensions.width} / ${videoDimensions.height}` : 'auto',
                        }}
                      >
                        <img 
                          src={getActiveViewUrl()} 
                          className="relative z-10 select-none shadow-2xl transition rounded-lg"
                          style={{ 
                            width: '100%',
                            height: '100%',
                            objectFit: 'contain',
                            imageRendering: 'pixelated'
                          }}
                          alt="Workspace preview output"
                        />

                        {/* Absolutely positioned canvas for custom pointer drawing (Trimaps / Protection Marks) */}
                        <canvas 
                          className={cn(
                            "absolute inset-0 z-20 cursor-crosshair opacity-75",
                            (currentTab === 'translucent' || cleanupProtectActive || stainPipetteActive) ? 'pointer-events-auto' : 'pointer-events-none'
                          )}
                          width={frames[previewIndex]?.blob ? Math.round(videoDimensions.width / scaleFactor || 64) : 64}
                          height={frames[previewIndex]?.blob ? Math.round(videoDimensions.height / scaleFactor || 64) : 64}
                          style={{
                            width: '100%',
                            height: '100%',
                            objectFit: 'contain'
                          }}
                          onMouseDown={(e) => {
                            if (currentTab === 'translucent') setIsDrawingTrimap(true);
                            if (currentTab === 'cleanup' && !stainPipetteActive) setIsDrawingProtect(true);
                            handleCanvasInteraction(e);
                          }}
                          onMouseMove={(e) => {
                            if (isDrawingTrimap || isDrawingProtect) {
                              handleCanvasInteraction(e);
                            }
                          }}
                          onMouseUp={() => {
                            setIsDrawingTrimap(false);
                            setIsDrawingProtect(false);
                          }}
                          onMouseLeave={() => {
                            setIsDrawingTrimap(false);
                            setIsDrawingProtect(false);
                          }}
                        />

                        {/* Semi-transparent protective overlay stencil for user helper visual mask */}
                        {currentTab === 'cleanup' && protectMasks[previewIndex] && (
                          <div className="absolute inset-0 pointer-events-none z-15 bg-red-500/20 mix-blend-multiply rounded-lg">
                            {/* Draws active protect coverage on image bounding box */}
                          </div>
                        )}
                      </div>
                    )}

                    {/* Playback details floating label */}
                    {frames.length > 0 && (
                      <div className="absolute bottom-4 left-4 z-30">
                        <div className="px-3 py-1.5 bg-slate-900/90 backdrop-blur rounded-xl text-[10px] font-mono font-bold text-white shadow flex items-center gap-3">
                          <Monitor className="w-3.5 h-3.5 text-indigo-400" />
                          {t('zoomNative').replace('{zoom}', String(scaleFactor))}
                          <span className="text-white/20">|</span>
                          FRAME {previewIndex + 1} / {frames.length}
                        </div>
                      </div>
                    )}

                    {/* Heavy algorithm processes loader */}
                    {(isProcessing || isMattingSequence || isQuantizing || isCleaningProgress) && (
                      <div className="absolute inset-0 bg-slate-950/70 backdrop-blur-sm flex flex-col items-center justify-center gap-4 z-40">
                        <div className="w-48 h-1.5 bg-slate-800 rounded-full overflow-hidden">
                          <motion.div 
                            className="h-full bg-indigo-500"
                            initial={{ width: 0 }}
                            animate={{ width: `${progress}%` }}
                          />
                        </div>
                        <p className="font-mono text-[9px] font-bold text-white tracking-[0.34em] uppercase">
                          {t('processing')} {progress}%
                        </p>
                      </div>
                    )}

                  </div>
                </div>

                {/* Animated sequential list footer */}
                {frames.length > 0 && (
                  <div className="flex flex-col gap-4 flex-1 min-h-0 bg-white border border-slate-200 rounded-3xl p-5 shadow-sm">
                    <h3 className="text-[10px] font-bold text-slate-500 uppercase tracking-widest flex items-center gap-2 font-mono ml-1">
                      <Layers className="w-3 h-3 text-indigo-500" />
                      Sequence Strip
                    </h3>
                    
                    <div className="flex-1 overflow-y-auto custom-scrollbar">
                      <div className="grid grid-cols-2 sm:grid-cols-4 md:grid-cols-6 gap-3 content-start">
                        {frames.map((frame, idx) => (
                          <motion.div 
                            key={frame.id}
                            initial={{ opacity: 0 }}
                            animate={{ opacity: 1 }}
                            onClick={() => {
                              setPreviewIndex(idx);
                              setIsPreviewing(false);
                            }}
                            className={cn(
                              "group aspect-square bg-slate-50 border p-1 rounded-2xl cursor-pointer transition-all hover:scale-[1.01] shadow-sm",
                              previewIndex === idx ? "ring-2 ring-indigo-500 border-indigo-500 bg-indigo-50/50" : "border-slate-100"
                            )}
                          >
                            <div className="w-full h-full rounded-xl relative overflow-hidden checkerboard flex items-center justify-center">
                              <img src={frame.dataUrl} className="max-w-[75%] max-h-[75%] pixelated relative z-10 transition-transform group-hover:scale-115" />
                              <div className="absolute bottom-1 right-1.5 text-[8px] font-mono font-bold text-slate-400 bg-white/75 px-1 rounded shadow-sm">
                                #{idx}
                              </div>
                            </div>
                          </motion.div>
                        ))}
                      </div>
                    </div>
                  </div>
                )}

              </div>
            )}
          </div>
        </section>
      </main>

      {/* Hidden processing canvas anchor */}
      <div className="hidden">
        <canvas ref={canvasRef} />
      </div>
    </div>
  );
}
