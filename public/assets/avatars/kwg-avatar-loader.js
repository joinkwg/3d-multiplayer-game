/* KWG 3D Online V3.58 — Modular GLB avatar asset loader (Three.js r128).
 * Artist-created GLBs only. A disabled/incomplete pack never replaces a live avatar.
 * Each GLB is a single style asset; internal rig-part groups are for animation.
 */
(function(global){
  'use strict';
  const PREFIX='/assets/avatars/';
  const PARTS={
    KWG_PART_TORSO:'torso', KWG_PART_HEAD:'head',
    KWG_PART_ARM_L:'leftArm', KWG_PART_ARM_R:'rightArm',
    KWG_PART_LEG_L:'leftLeg', KWG_PART_LEG_R:'rightLeg',
    KWG_PART_EYES:'eyes', KWG_PART_MOUTH:'head'
  };
  const REQUIRED=['tops','bottoms','shoes','hair','heads','eyes','mouths'];
  const VALID=new Set(['tops','bottoms','shoes','hair','heads','eyes','mouths','skincolors','flightsuits']);
  const cache=new Map();
  let manifestPromise=null;
  function loadManifest(){
    if(!manifestPromise){
      manifestPromise=fetch(PREFIX+'manifest.json',{cache:'no-cache'})
        .then(r=>{if(!r.ok)throw new Error('Avatar manifest HTTP '+r.status);return r.json();})
        .catch(err=>{console.warn('KWG avatar pack manifest unavailable:',err);return {enabled:false};});
    }
    return manifestPromise;
  }
  function assetURL(relative){
    if(typeof relative!=='string'||!relative||relative.startsWith('/')||relative.includes('..')||/^[a-z]+:/i.test(relative)||relative.includes('\\')){
      throw new Error('Avatar asset paths must be relative paths inside '+PREFIX);
    }
    return PREFIX+relative;
  }
  function loadScene(path){
    const url=assetURL(path);
    if(!cache.has(url)){
      cache.set(url,new Promise((resolve,reject)=>{
        if(!global.THREE||!global.THREE.GLTFLoader){reject(new Error('Three.js GLTFLoader missing'));return;}
        new global.THREE.GLTFLoader().load(url,gltf=>resolve(gltf.scene),undefined,reject);
      }));
    }
    return cache.get(url).then(scene=>scene.clone(true));
  }
  function rig(){
    const T=global.THREE;
    const root=new T.Group();root.name='KWG_MODULAR_RIG';
    const torso=new T.Group();torso.name='KWG_RIG_TORSO';root.add(torso);
    const head=new T.Group();head.name='KWG_RIG_HEAD';head.position.set(0,2.12,0);root.add(head);
    const eyes=new T.Group();eyes.name='KWG_RIG_EYES';head.add(eyes);
    const leftArm=new T.Group(),rightArm=new T.Group();
    leftArm.name='KWG_RIG_ARM_L';rightArm.name='KWG_RIG_ARM_R';
    leftArm.position.set(-.354,1.55,0);rightArm.position.set(.354,1.55,0);
    root.add(leftArm,rightArm);
    const leftLeg=new T.Group(),rightLeg=new T.Group();
    leftLeg.name='KWG_RIG_LEG_L';rightLeg.name='KWG_RIG_LEG_R';
    leftLeg.position.set(-.174,.92,0);rightLeg.position.set(.174,.92,0);
    root.add(leftLeg,rightLeg);
    root.userData.limbs={leftArm,rightArm,leftLeg,rightLeg,torso};
    root.userData.blinkEyes=eyes;
    root.userData.blinkClock=2.5;
    return {root,anchors:{torso,head,eyes,leftArm,rightArm,leftLeg,rightLeg}};
  }
  function tint(scene,color,category){
    if(!color)return;
    scene.traverse(node=>{
      if(!node.isMesh||!node.material)return;
      const recolor=(mat)=>{
        if(!mat||!mat.name)return mat;
        const name=mat.name.toUpperCase();
        const matches=name.includes('KWG_TINT')||
          (category==='skincolors'&&name.includes('KWG_SKIN'))||
          (category==='hair'&&name.includes('KWG_HAIR'));
        if(!matches)return mat;
        const copy=mat.clone();if(copy.color)copy.color.set(color);return copy;
      };
      node.material=Array.isArray(node.material)?node.material.map(recolor):recolor(node.material);
    });
  }
  function attach(scene,anchors,defaultAnchor){
    const named=[];
    scene.traverse(node=>{if(PARTS[node.name])named.push(node);});
    if(named.length){
      // Do not attach nested part groups twice.
      const roots=named.filter(node=>{let p=node.parent;while(p){if(named.includes(p))return false;p=p.parent;}return true;});
      for(const part of roots){
        const dest=anchors[PARTS[part.name]];
        if(dest){part.parent?.remove(part);dest.add(part);}
      }
    }else{
      const anchor=anchors[defaultAnchor];
      if(!anchor)throw new Error('Unknown avatar attachment '+defaultAnchor);
      anchor.add(scene);
    }
  }
  function styleEntry(manifest,category,cosmetics){
    const item=cosmetics?.[category];
    const style=item?.metadata?.style;
    const choices=manifest.styles?.[category]||{};
    return {item,style,definition:style?choices[style]:null};
  }
  async function createAvatar(manifest,cosmetics){
    if(!manifest.enabled||!manifest.base)return null;
    const required=REQUIRED.map(cat=>[cat,styleEntry(manifest,cat,cosmetics)]);
    if(required.some(([cat,v])=>!v.definition?.file))return null;
    const optional=['skincolors','flightsuits'].map(cat=>[cat,styleEntry(manifest,cat,cosmetics)]);
    // Missing optional style assets are not silently replaced by wrong clothing.
    if(optional.some(([cat,v])=>v.style&&!v.definition?.file&&cat==='flightsuits'))return null;
    const selected=[...required,...optional.filter(([cat,v])=>v.definition?.file)];
    const [base,...files]=await Promise.all([
      loadScene(manifest.base),...selected.map(([cat,v])=>loadScene(v.definition.file))
    ]);
    const result=rig();
    tint(base,cosmetics?.skincolors?.metadata?.color,'skincolors');
    attach(base,result.anchors,'torso');
    for(let i=0;i<selected.length;i++){
      const [category,v]=selected[i];
      const file=files[i];
      tint(file,v.item?.metadata?.color,category);
      attach(file,result.anchors,v.definition.anchor||({hair:'head',heads:'head',eyes:'eyes',mouths:'head',shoes:'leftLeg'}[category]||'torso'));
    }
    result.root.userData.hasFlightsuit=!!cosmetics?.flightsuits;
    return result.root;
  }
  async function upgrade(avatar,app,cosmetics){
    if(!avatar||!avatar.userData)return false;
    const manifest=await loadManifest();
    if(!manifest.enabled)return false;
    const existing=avatar.children.slice();
    let replacement;
    try{replacement=await createAvatar(manifest,cosmetics);}catch(err){
      console.warn('KWG modular GLB failed; retaining procedural avatar:',err);return false;
    }
    if(!replacement||!avatar.parent||avatar.userData.kwgModularActive)return false;
    for(const child of existing){if(child.parent===avatar)avatar.remove(child);}
    avatar.add(replacement);
    avatar.userData.limbs=replacement.userData.limbs;
    avatar.userData.blinkEyes=replacement.userData.blinkEyes;
    avatar.userData.blinkClock=replacement.userData.blinkClock;
    avatar.userData.kwgModularActive=true;
    return true;
  }
  global.KWGAvatarAssets={loadManifest,loadScene,createAvatar,upgrade,rig,parts:PARTS};
})(window);
