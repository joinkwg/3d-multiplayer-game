# KWG Modular Avatar Art Contract — V3.58

## Status

This is a **working loader and preview workbench**, not a finished avatar-art replacement. The reference-quality meshes do **not** exist yet. `manifest.json` is deliberately `enabled: false` so the current game keeps working and does not load nonexistent files. Enabling it without complete GLBs is not supported. Server, inventory, purchases, and flightsuit gameplay are unchanged.

## What an artist exports

Author **one GLB per clothing/hairstyle/head/shoe style**, reusing its geometry for all the purchasable color variants. A GLB may contain multiple **connected, sculpted mesh sections** for animation, but should not be assembled from primitive spheres/boxes. The GLB may have nodes named `KWG_PART_TORSO`, `KWG_PART_HEAD`, `KWG_PART_ARM_L`, `KWG_PART_ARM_R`, `KWG_PART_LEG_L`, `KWG_PART_LEG_R`, `KWG_PART_EYES`, `KWG_PART_MOUTH`. The loader attaches each named node to the shared animated rig; any unnamed scene is attached to the `anchor` in the manifest. In practice a shirt needs torso and both sleeve/arm parts, pants need two leg parts, and shoes need left/right parts. **Rigid pivot animation** is supported at this stage; fully deforming skinned GLBs will need a subsequent skin-binding integration.

Coordinate system: **Y up, Z forward**, avatar feet at Y=0, head centered around Y=2.12, total avatar height approximately 2.6–2.75. The shared rig pivot points (world-space) are:

- Head: `(0, 2.12, 0)`
- Left arm: `(-0.354, 1.55, 0)`
- Right arm: `(0.354, 1.55, 0)`
- Left leg: `(-0.174, 0.92, 0)`
- Right leg: `(0.174, 0.92, 0)`

The vertices of a `KWG_PART_*` node are **local to that pivot**. For example, a left sleeve starts near `(0, 0, 0)` inside `KWG_PART_ARM_L`. Use matching seam widths and proportions for every clothing item; do not scale each garment independently at runtime. Name the material intended for color variants `KWG_TINT`; name body skin material `KWG_SKIN`, hair material `KWG_HAIR`. The loader clones tintable materials before recoloring, so different players can wear different colors. Artists can use custom UV textures and PBR materials for authored detail. Do not bake skin/clothing colors into the geometry if the item has purchasable variants.

## Asset structure

`public/assets/avatars/base/body.glb` is the underlying shared body. Other style GLBs go into `tops/`, `bottoms/`, `shoes/`, `hair/`, `heads/`, `eyes/`, `mouths/`, `flightsuits/`. In `manifest.json`, each style key must exactly match the existing item `metadata.style` value. Missing styles cause that avatar to remain on the legacy model; **the shop and ownership data are not changed**. When an artist has delivered a complete compatible set, change `enabled` to `true` and deploy all the referenced GLBs together. Each style/color item in the server catalog continues to have its own price and ownership record.

## Testing

Open `/avatar-workbench.html` in the running game to inspect GLBs. Load a model and inspect its bounding box, mesh/material names and pivot groups. The workbench is a **technical preview**; it is not a replacement for evaluating artistic quality against the supplied JumpStart references. Test one complete avatar first, including a head, hair, face, top, pants, and sneakers, before building the full catalog. Ensure walking, jumping, blinking and gliding remain correct. The workbench is a local-file inspector and does not upload or save anything.

## Important limitations

- This version adds the **asset-loading infrastructure**, but does not contain professionally modeled GLBs. Avatar appearance remains the previous version until a complete compatible pack is deployed.
- Store/profile 2D thumbnails currently use the synchronous legacy model; their rendering needs to be switched to asynchronous GLB captures once the first real pack is approved.
- Rigid attachment groups support existing movement; smooth skin deformation, geometry occlusion between outfits, and advanced facial morph targets require further work once the final base rig is selected.
- The game keeps its existing WebGL and Socket.IO dependencies; no server changes or database migration are needed for this foundation.
