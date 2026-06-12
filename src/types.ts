export interface SpriteFrame {
  id: string;
  dataUrl: string;
  blob: Blob;
  index: number;
  coreDataUrl?: string; // Translucent core matte layer
  glowDataUrl?: string; // Translucent glow matte layer
}

export type AppTab = 'video' | 'batch' | 'translucent' | 'cleanup' | 'glowCleanup' | 'glowColorSimplify';

export type Language = 'zh' | 'en';

export type PreviewMode = 'source' | 'trimap' | 'core' | 'glow' | 'final';

export type BlendMode = 'normal' | 'screen' | 'add';

export type BackdropColor = 'transparent' | 'white' | 'black' | 'green' | 'pink';
