/* Six-object GLB wardrobe runtime. Geometry is loaded from authored assets;
   only texture composition and bone/morph animation happen at runtime. */
(function(global){
'use strict';
const ROOT='/assets/avatars/',templates=new Map(),pictures=new Map(),paints=new Map();let manifest,ready=false;
const categories={hair:'hair',head:'heads',top:'tops',bottom:'bottoms',leftshoe:'shoes',rightshoe:'shoes'};
const status=document.getElementById('avatar-assets-status');
const image=url=>new Promise((resolve,reject)=>{const im=new Image();im.onload=()=>resolve(im);im.onerror=()=>reject(new Error('Could not load '+url));im.src=url;});
async function load(){
 if(!global.THREE?.GLTFLoader)throw new Error('Three.js GLTFLoader is unavailable.');
 const response=await fetch(ROOT+'manifest.json');if(!response.ok)throw new Error('Avatar manifest missing ('+response.status+'). Upload the assets folder.');manifest=await response.json();
 const jobs=Object.entries(manifest.templates).map(([key,spec])=>async()=>{
  const gltf=await new Promise((resolve,reject)=>new THREE.GLTFLoader().load(spec.url,resolve,undefined,reject));let mesh;
  gltf.scene.traverse(o=>{if(o.isSkinnedMesh){if(mesh)throw new Error('Template has more than one mesh: '+key);mesh=o;}});
  if(!mesh)throw new Error('Template has no skinned mesh: '+key);
  templates.set(key,{geometry:mesh.geometry,image:mesh.material.map.image,source:mesh});
 });
 const eyeStyles=['bright','lashes','sleepy','round','anime','angry','stars','robot','cyclops'];
 for(const s of eyeStyles)for(const suffix of ['', '-closed'])jobs.push(async()=>pictures.set('eyes-'+s+suffix,await image(ROOT+'faces/eyes-'+s+suffix+'.png')));
 for(const s of ['smile','grin','open','smirk','pout','surprised','lipstick','fangs','monster','cat','stitched','beak'])jobs.push(async()=>pictures.set('mouth-'+s,await image(ROOT+'faces/mouth-'+s+'.png')));
 let cursor=0,completed=0;await Promise.all(Array.from({length:4},async()=>{while(cursor<jobs.length){const j=jobs[cursor++];await j();completed++;if(status)status.textContent='Loading avatar artwork… '+Math.round(completed/jobs.length*100)+'%';}}));ready=true;
}
const rgb=s=>{const n=parseInt((s||'#ffffff').slice(1),16);return [n>>16&255,n>>8&255,n&255];};
function canvas(size=512){const c=document.createElement('canvas');c.width=c.height=size;return c;}
function pattern(ctx,color,kind,x=0,y=0,w=512,h=512){
 ctx.save();ctx.beginPath();ctx.rect(x,y,w,h);ctx.clip();ctx.fillStyle=color;ctx.fillRect(x,y,w,h);
 const g=ctx.createRadialGradient(x+w*.45,y+h*.4,0,x+w*.45,y+h*.4,Math.max(w,h)*.8);g.addColorStop(0,'rgba(255,237,205,.10)');g.addColorStop(1,'rgba(65,30,30,.12)');ctx.fillStyle=g;ctx.fillRect(x,y,w,h);
 if(kind==='rainbow'){const grad=ctx.createLinearGradient(x,y,x+w,y+h);['#ef737c','#f3c957','#80c886','#76ced8','#968be1'].forEach((c,i)=>grad.addColorStop(i/4,c));ctx.fillStyle=grad;ctx.fillRect(x,y,w,h);}
 else if(kind==='chrome'){const grad=ctx.createLinearGradient(x,y,x+w,y);['#5f7888','#d9ecf2','#8baabf','#dce9ec','#597a90'].forEach((c,i)=>grad.addColorStop(i/4,c));ctx.fillStyle=grad;ctx.fillRect(x,y,w,h);}
 else if(kind&&kind!=='solid'){
  ctx.globalAlpha=kind==='freckles'?.32:.48;ctx.fillStyle=kind==='stars'?'#ffe7a2':'#5b463a';ctx.strokeStyle=kind==='lava'?'#ff9955':'#f5efcf';ctx.lineWidth=2;
  for(let yy=y;yy<y+h;yy+=23)for(let xx=x;xx<x+w;xx+=24){
   if(kind==='stars'){ctx.beginPath();for(let i=0;i<10;i++){const a=i*Math.PI/5,r=i%2?2:6;ctx.lineTo(xx+10+Math.sin(a)*r,yy+10+Math.cos(a)*r);}ctx.fill();}
   else if(kind==='scales'){ctx.beginPath();ctx.arc(xx+(yy%46?12:0),yy,12,0,Math.PI);ctx.stroke();}
   else if(kind==='marble'||kind==='lava'){ctx.beginPath();ctx.moveTo(xx,yy);ctx.bezierCurveTo(xx+22,yy+4,xx-12,yy+29,xx+10,yy+36);ctx.stroke();}
   else if(kind==='candy'){ctx.fillStyle='#fff1dc';ctx.fillRect(xx,yy,7,24);}
   else{ctx.beginPath();ctx.arc(xx+7,yy+9,1.5,0,7);ctx.fill();}
  }
 }
 ctx.restore();
}
function layer(ctx,key,color,eye=false){
 const source=pictures.get(key);if(!source)return;
 const c=canvas();const t=c.getContext('2d');t.drawImage(source,0,0,512,512);const pixels=t.getImageData(0,0,512,512),a=pixels.data,target=rgb(color),base=eye?[99,185,207]:[189,65,105];
 for(let i=0;i<a.length;i+=4){if(!a[i+3])continue;const r=a[i],g=a[i+1],b=a[i+2];const colored=eye?(b>r*1.14&&g>r*1.08):(r>g*1.35&&r>55);
  if(colored)for(let j=0;j<3;j++)a[i+j]=Math.min(255,a[i+j]*target[j]/base[j]);
 }
 t.putImageData(pixels,0,0);ctx.drawImage(c,0,0);
}
function painted(slot,spec,look,source,closed=false){
 const c=canvas(),ctx=c.getContext('2d'),skin=look.skincolors||{},col=spec.color||'#506784';
 if(slot==='head'){
  pattern(ctx,skin.color||'#c68f56',skin.pattern||'solid');const eyes=look.eyes||{},mouth=look.mouths||{};
  layer(ctx,'eyes-'+(eyes.style||'bright')+(closed?'-closed':''),eyes.color||'#63b9cf',true);
  layer(ctx,'mouth-'+(mouth.style||'smile'),mouth.color||'#61333e');
  ctx.strokeStyle='#483126';ctx.lineWidth=1.7;ctx.beginPath();ctx.moveTo(256,289);ctx.lineTo(252,296);ctx.lineTo(258,302);ctx.stroke();
 }else{
  ctx.drawImage(source,0,0,512,512);const pixels=ctx.getImageData(0,0,512,512),p=pixels.data;
  const base=rgb(slot==='hair'?'#654123':slot==='top'?'#8c2730':slot==='bottom'?'#303542':'#22282e'),target=rgb(col),skinBase=[198,143,86],skinColor=rgb(skin.color||'#c68f56');
  for(let i=0;i<p.length;i+=4){const pixel=i/4,x=pixel%512,y=Math.floor(pixel/512);const skinRegion=slot!=='hair'&&x>=384&&!((slot==='leftshoe'||slot==='rightshoe')&&y>=399);
   if(skinRegion){for(let k=0;k<3;k++)p[i+k]=Math.min(255,p[i+k]*skinColor[k]/skinBase[k]);}
   else if(slot==='hair'||x<384){const hi=Math.max(p[i],p[i+1],p[i+2]),lo=Math.min(p[i],p[i+1],p[i+2]);if(!(hi>170&&hi-lo<60))for(let k=0;k<3;k++)p[i+k]=Math.min(255,p[i+k]*target[k]/Math.max(base[k],1));}
  }
  ctx.putImageData(pixels,0,0);
  if(slot!=='hair'&&skin.pattern&&skin.pattern!=='solid')pattern(ctx,skin.color,skin.pattern,390,0,122,(slot==='leftshoe'||slot==='rightshoe')?399:512);
  if(slot==='top'&&spec.style?.startsWith('flight_')){
   const design=spec.style.slice(7);ctx.save();ctx.strokeStyle='#e3e7cb';ctx.fillStyle='#b6dfd9';ctx.lineWidth=3;
   if(design==='racer'){for(const x of [38,332])ctx.fillRect(x,20,11,220);}
   if(design==='dragon'){for(let y=50;y<220;y+=23){ctx.beginPath();ctx.moveTo(0,y);ctx.lineTo(18,y+9);ctx.lineTo(0,y+18);ctx.stroke();}}
   if(design==='butterfly'){for(const x of [58,326]){ctx.beginPath();ctx.ellipse(x,170,24,37,0,0,7);ctx.stroke();}}
   if(design==='cosmic'){for(let k=0;k<28;k++){const x=(k*97)%378,y=(k*59)%245;ctx.fillRect(x,y,3,3);}}
   ctx.restore();
  }
 }
 const tex=new THREE.CanvasTexture(c);tex.flipY=false;tex.anisotropy=2;tex.userData={avatarShared:true};return tex;
}
function acquire(slot,key,spec,look){
 const cacheKey=JSON.stringify([slot,key,spec,look.skincolors,slot==='head'?look.eyes:null,slot==='head'?look.mouths:null]);let entry=paints.get(cacheKey);
 if(!entry){const template=templates.get(key),open=painted(slot,spec,look,template.image),closed=slot==='head'?painted(slot,spec,look,template.image,true):null;
  const material=new THREE.MeshLambertMaterial({map:open,color:0xeeeeee,side:THREE.DoubleSide,skinning:true,morphTargets:slot==='top'});material.userData.avatarShared=true;
  entry={key:cacheKey,material,open,closed,refs:0};paints.set(cacheKey,entry);
 }
 entry.refs++;return entry;
}
function prune(){if(paints.size<=64)return;for(const [key,e] of paints){if(e.refs===0){e.material.dispose();e.open.dispose();e.closed?.dispose();paints.delete(key);if(paints.size<=64)break;}}}
// Lower-body proportions (X axis only): preserve height and mesh detailing.
// These are conservative starting values; adjust after viewing your GLBs.
const LOWER_FIT={pantsWidth:0.88,shoeSpacing:0.88,shoeWidth:0.97};
const fittedGeometries=new Map();
function fittedGeometry(key,slot,original){
 if(slot!=='bottom'&&slot!=='leftshoe'&&slot!=='rightshoe')return original;
 if(fittedGeometries.has(key))return fittedGeometries.get(key);
 const geometry=original.clone(),position=geometry.attributes.position;
 if(!position)return original;
 original.computeBoundingBox();
 const center=(original.boundingBox.min.x+original.boundingBox.max.x)/2;
 const shoe=slot==='leftshoe'||slot==='rightshoe';
 for(let i=0;i<position.count;i++){
  const x=position.getX(i);
  position.setX(i,shoe?center*LOWER_FIT.shoeSpacing+(x-center)*LOWER_FIT.shoeWidth:x*LOWER_FIT.pantsWidth);
 }
 position.needsUpdate=true;
 geometry.computeBoundingBox();geometry.computeBoundingSphere();
 fittedGeometries.set(key,geometry);
 return geometry;
}
function build(look){
 if(!ready)throw new Error('Avatar GLB assets have not finished loading.');
 const group=new THREE.Group();group.name='avatar';const bones=manifest.joints.map(([name])=>{const b=new THREE.Bone();b.name=name;return b;});
 manifest.joints.forEach(([,parent,position],i)=>{const pp=parent<0?[0,0,0]:manifest.joints[parent][2];bones[i].position.set(position[0]-pp[0],position[1]-pp[1],position[2]-pp[2]);(parent<0?group:bones[parent]).add(bones[i]);});
 group.updateMatrixWorld(true);const skeleton=new THREE.Skeleton(bones);skeleton.calculateInverses();
 const flight=look.flightsuits;const slotSpecs={hair:look.hair,head:look.heads,top:flight?{...flight,style:'flight_'+flight.style}:look.tops,bottom:flight?{...flight,style:'pants'}:look.bottoms,leftshoe:look.shoes,rightshoe:look.shoes};
 const meshes={};for(const slot of manifest.meshNames){const spec=slotSpecs[slot];const key=slot+'-'+spec.style;const template=templates.get(key);if(!template)throw new Error('Missing avatar part '+key);
  const paint=acquire(slot,key,spec,look);const material=slot==='head'?paint.material.clone():paint.material;
  const mesh=new THREE.SkinnedMesh(fittedGeometry(key,slot,template.geometry),material);mesh.name=slot;mesh.userData.avatarPart=true;mesh.userData.avatarPaint=paint;mesh.userData.avatarSharedGeometry=true;mesh.castShadow=true;mesh.receiveShadow=true;mesh.frustumCulled=false;mesh.bind(skeleton,new THREE.Matrix4());group.add(mesh);meshes[slot]=mesh;
  if(slot==='head')group.userData.blink={mesh,openMap:paint.open,closedMap:paint.closed,time:2+Math.random()*3,closed:false};
 }
 group.userData.avatarMeshes=meshes;group.userData.avatarSkeleton=skeleton;group.userData.hasFlightsuit=!!flight;
 group.userData.limbs={leftArm:bones[5],rightArm:bones[8],leftLeg:bones[11],rightLeg:bones[14],torso:bones[2]};return group;
}
function blink(group,dt){const b=group?.userData?.blink;if(!b)return;b.time-=Math.min(dt||.016,.1);if(b.time<=0){b.closed=!b.closed;b.time=b.closed?.12:2.5+Math.random()*4;b.mesh.material.map=b.closed?b.closedMap:b.openMap;}}
function glide(group,value){const mesh=group?.userData?.avatarMeshes?.top;if(mesh?.morphTargetInfluences?.length)mesh.morphTargetInfluences[0]=value?1:0;}
function dispose(group){if(group?.userData?.avatarDisposed)return;if(group?.userData)group.userData.avatarDisposed=true;group?.traverse(o=>{if(o.userData.avatarPart){o.userData.avatarPaint.refs=Math.max(0,o.userData.avatarPaint.refs-1);if(o.name==='head')o.material.dispose();}});group?.userData?.avatarSkeleton?.dispose();prune();}
global.AvatarGLB={ready:load(),build,blink,glide,dispose,get manifest(){return manifest;},get loaded(){return ready;}};
})(window);
