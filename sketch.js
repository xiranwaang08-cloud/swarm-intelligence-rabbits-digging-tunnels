/* ============================================================================
   SUBTERRANEAN SWARM :: ALGORITHMIC RABBIT BURROWS
   ----------------------------------------------------------------------------
   Minecraft/Stardew-style cross-section of soil, topped by a small wooden
   cabin. Click anywhere in the dirt to drop a rabbit that immediately
   starts digging. Emergent tunnel networks arise from three local rules,
   with NO central planner:

     1. STIGMERGY / MERGE-INTO-TUNNEL  -> converges paths into thick trunks
     2. CROWD-REPULSION BRANCHING       -> spreads paths into fresh dirt
     3. PROXIMITY REPRODUCTION + ENERGY DEATH -> population dynamics

   NARRATIVE LAYER (new): the cabin's foundation zone tracks how hollowed-out
   the soil directly beneath it has become. As rabbits over-excavate that
   zone, the cabin shakes, sheds dust, and eventually collapses into the
   burrow -- search "CABIN LOGIC:" to jump to that system.

   Search "SWARM LOGIC:" to jump straight to each swarm-intelligence rule.
   ============================================================================ */

// ---------------------------------------------------------------------------
// 1. GLOBAL CONFIG
//    NOTE: constants needing PI/TWO_PI use Math.PI -- p5's PI isn't attached
//    to globals until AFTER p5 boots, but these top-level consts run on load.
// ---------------------------------------------------------------------------
const CELL_SIZE           = 6;
const TARGET_WIDTH         = 800;
const TARGET_GRID_HEIGHT   = 560;
const GRASS_HEIGHT         = 10;
const PANEL_HEIGHT         = 90;
const SWARM_BUTTON_COUNT   = 10;
const MAX_AGENTS           = 260;

// --- Movement: spatial Perlin flow field ------------------------------------
const FLOW_NOISE_SCALE     = 0.012;
const FLOW_TIME_SCALE      = 0.0012;
const FLOW_ANGLE_SPAN      = 4;
const TURN_SMOOTH          = 0.10;
const BASE_SPEED           = 1.05;
const GRAVITY_BIAS         = 0.16;
const OUTWARD_BIAS         = 0.10;

const ENERGY_MIN_START     = 260;
const ENERGY_MAX_START     = 420;
const ENERGY_DECAY_PER_FRAME = 0.35;
const ROCK_COLLISION_ENERGY_COST = 0.6;

// --- Merge-into-tunnel sensing ------------------------------------------------
const MERGE_SENSE_RADIUS   = 3;
const MERGE_MIN_INTENSITY  = 1.5;
const MERGE_CHANCE         = 0.65;
const MERGE_PULL_STRENGTH  = 0.6;
const SELF_TRAIL_MEMORY    = 26;

// --- Crowd-repulsion branching ------------------------------------------------
const DENSITY_RADIUS_CELLS = 2;
const DENSITY_BRANCH_THRESHOLD = 6;
const BRANCH_CHANCE        = 0.02;
const BRANCH_ENERGY_COST   = 55;

const REPRO_CHANCE         = 0.012;
const REPRO_ENERGY_COST    = 30;

const INTENSITY_MAX        = 42;
const PHEROMONE_MAX        = 30;
const PHEROMONE_DECAY      = 0.986;
const INITIAL_AGENTS       = 5;

// Auto-reset now only fires on one of two NARRATIVE end states (see draw()):
// the cabin has been fully collapsed for a few seconds, or the soil is
// almost entirely excavated. No arbitrary timer or agent-count cap.
const MAX_TUNNEL_COVERAGE  = 0.88;
const COLLAPSED_HOLD_SECONDS = 3;

const ROCK_NOISE_SCALE     = 0.11;
const ROCK_THRESHOLD       = 0.62;

// Precomputed neighbor-offset lists (built ONCE at load -- never in a hot
// loop). Per-agent sensing below iterates these with .forEach() rather than
// a raw nested for-loop, since raw for/while loops that run every frame are
// what tripped the Web Editor's "infinite loop detected" guard previously.
const MERGE_OFFSETS = [];
for (let dr = -MERGE_SENSE_RADIUS; dr <= MERGE_SENSE_RADIUS; dr++) {
  for (let dc = -MERGE_SENSE_RADIUS; dc <= MERGE_SENSE_RADIUS; dc++) {
    if (dc === 0 && dr === 0) continue;
    MERGE_OFFSETS.push({ dc, dr });
  }
}
const DENSITY_OFFSETS = [];
for (let dr = -DENSITY_RADIUS_CELLS; dr <= DENSITY_RADIUS_CELLS; dr++) {
  for (let dc = -DENSITY_RADIUS_CELLS; dc <= DENSITY_RADIUS_CELLS; dc++) {
    DENSITY_OFFSETS.push({ dc, dr });
  }
}

// --- CABIN LOGIC: narrative layer config -------------------------------------
const CABIN_W              = 60;
const CABIN_H              = 40;
const CABIN_AREA_H         = 56;   // reserved space above the grass for the cabin + HUD
const FOUNDATION_ROWS      = 14;   // "top 10-15 grid rows" directly under the cabin
const HEALTH_WARNING       = 60;   // % -- below this, Phase 2 (shake + dust)
const HEALTH_COLLAPSE      = 30;   // % -- below this, Phase 3 (collapse)
const COLLAPSE_DURATION_FRAMES = 70;
const DUST_SPAWN_CHANCE    = 0.35;
const MAX_DUST             = 40;
const SHAKE_MAX            = 3;    // px, at the collapse threshold

// Palette --------------------------------------------------------------------
let COL_GRASS, COL_TUNNEL_DARK, COL_GLOW_LOW, COL_GLOW_HIGH, COL_STONE, COL_HEAD;
let COL_PANEL_BG, COL_PANEL_BORDER, COL_BTN, COL_BTN_HOVER, COL_BTN_TEXT;
let COL_SKY, COL_WOOD, COL_WOOD_DARK, COL_ROOF, COL_WINDOW, COL_CHIMNEY, COL_DUST;

// ---------------------------------------------------------------------------
// 2. SHARED ENVIRONMENT (the "soil")
// ---------------------------------------------------------------------------
let cols, rows;
let gridPixelW, gridPixelH;
let grassY, gridTopY, gridBottomY;
let canvasW, canvasH;

let intensityGrid;
let pheromoneGrid;
let rockGrid;
let dirtShade;
let agentCountGrid;

let agents = [];
let isRunning = true;
let buttons = [];

let generation = 1;

let soilRowsDrawn = 0;
let soilFullyDrawn = false;
const SOIL_ROWS_PER_FRAME = 12;

let lastClickMs = -1000;
const CLICK_DEBOUNCE_MS = 150;

// --- CABIN LOGIC: runtime state -----------------------------------------------
let GRASS_TUFTS = [];
let MOON_X, MOON_Y;
let MOON_CELLS = [];
let STARS = [];
let foundationColStart, foundationColEnd;
let FOUNDATION_INDICES = [];
let foundationHealth = 100;
let cabinState = 'intact'; // 'intact' | 'warning' | 'collapsing' | 'collapsed'
let collapseTimer = 0;
let collapsedHoldTimer = 0; // frames spent in the 'collapsed' state, for the 3s delay
let dustParticles = [];
let collapsePieces = [];

function idx(c, r) { return r * cols + c; }

function toCell(x, y) {
  const c = floor(x / CELL_SIZE);
  const r = floor((y - gridTopY) / CELL_SIZE);
  return { c, r };
}

function inGridArea(y) { return y >= gridTopY && y < gridBottomY; }

function lerpAngle(a, b, t) {
  let diff = ((b - a + PI) % TWO_PI + TWO_PI) % TWO_PI - PI;
  return a + diff * t;
}

// ---------------------------------------------------------------------------
// 3. SOIL GENERATION / RENDERING
// ---------------------------------------------------------------------------
function generateSoil() {
  intensityGrid  = new Float32Array(cols * rows);
  pheromoneGrid  = new Float32Array(cols * rows);
  rockGrid       = new Uint8Array(cols * rows);
  dirtShade      = new Float32Array(cols * rows);
  agentCountGrid = new Uint16Array(cols * rows);

  const seedX = random(1000), seedY = random(1000);
  for (let r = 0; r < rows; r++) {
    for (let c = 0; c < cols; c++) {
      const i = idx(c, r);
      dirtShade[i] = random(-12, 12);
      if (r > 2) {
        const n = noise(seedX + c * ROCK_NOISE_SCALE, seedY + r * ROCK_NOISE_SCALE);
        rockGrid[i] = n > ROCK_THRESHOLD ? 1 : 0;
      }
    }
  }
}

function soilColor(i) {
  const shade = dirtShade[i];
  if (rockGrid[i]) {
    return color(
      constrain(120 + shade, 70, 170),
      constrain(112 + shade * 0.9, 65, 160),
      constrain(102 + shade * 0.8, 60, 150)
    );
  }
  return color(
    constrain(93 + shade, 50, 150),
    constrain(63 + shade * 0.8, 30, 110),
    constrain(41 + shade * 0.6, 15, 80)
  );
}

function tunnelGlowColor(i) {
  const p = constrain(pheromoneGrid[i] / PHEROMONE_MAX, 0, 1);
  const c = lerpColor(COL_GLOW_LOW, COL_GLOW_HIGH, p);
  return color(red(c), green(c), blue(c), map(p, 0, 1, 70, 255));
}

function drawCell(c, r) {
  const i = idx(c, r);
  const px = c * CELL_SIZE;
  const py = gridTopY + r * CELL_SIZE;

  if (intensityGrid[i] > 0) {
    noStroke();
    fill(COL_TUNNEL_DARK);
    rect(px, py, CELL_SIZE, CELL_SIZE);

    const glow = tunnelGlowColor(i);
    stroke(glow);
    strokeWeight(1.4);

    const leftDug   = c > 0 && intensityGrid[idx(c - 1, r)] > 0;
    const rightDug  = c < cols - 1 && intensityGrid[idx(c + 1, r)] > 0;
    const upDug     = r > 0 && intensityGrid[idx(c, r - 1)] > 0;
    const downDug   = r < rows - 1 && intensityGrid[idx(c, r + 1)] > 0;

    if (!upDug)    line(px, py, px + CELL_SIZE, py);
    if (!downDug)  line(px, py + CELL_SIZE, px + CELL_SIZE, py + CELL_SIZE);
    if (!leftDug)  line(px, py, px, py + CELL_SIZE);
    if (!rightDug) line(px + CELL_SIZE, py, px + CELL_SIZE, py + CELL_SIZE);

  } else {
    noStroke();
    fill(soilColor(i));
    rect(px, py, CELL_SIZE, CELL_SIZE);
  }
}

function redrawWithNeighbors(c, r) {
  drawCell(c, r);
  if (c > 0) drawCell(c - 1, r);
  if (c < cols - 1) drawCell(c + 1, r);
  if (r > 0) drawCell(c, r - 1);
  if (r < rows - 1) drawCell(c, r + 1);
}

function startSoilReveal() { soilRowsDrawn = 0; soilFullyDrawn = false; }

function stepSoilReveal() {
  const endRow = min(soilRowsDrawn + SOIL_ROWS_PER_FRAME, rows);
  noStroke();
  for (let r = soilRowsDrawn; r < endRow; r++) {
    for (let c = 0; c < cols; c++) drawCell(c, r);
  }
  soilRowsDrawn = endRow;
  if (soilRowsDrawn >= rows) soilFullyDrawn = true;
}

// Grass tuft x-positions are generated ONCE (in setup) and reused every
// frame -- both to avoid a growing per-frame loop and because re-randomizing
// them every frame would just look like flickering noise, not grass.
function buildGrassTufts() {
  GRASS_TUFTS = [];
  for (let x = 0; x < canvasW; x += 4) GRASS_TUFTS.push(x + random(-1, 1));
}

function drawSky() {
  noStroke();
  fill(COL_SKY);
  rect(0, 0, canvasW, grassY);
}

// Crescent moon, rasterized ONCE into a small grid of lit cells (rather
// than drawn with smooth ellipse()) so it reads as blocky pixel art
// consistent with the rest of the scene. The crescent shape comes from
// keeping cells inside a big circle but outside a smaller, offset circle.
function buildMoonBitmap() {
  MOON_CELLS = [];
  const R = 4.2, innerR = 3.8, offsetX = 2.4, offsetY = -1.6;
  for (let gy = -5; gy <= 5; gy++) {
    for (let gx = -5; gx <= 5; gx++) {
      const d1 = Math.sqrt(gx * gx + gy * gy);
      const d2 = Math.sqrt((gx - offsetX) * (gx - offsetX) + (gy - offsetY) * (gy - offsetY));
      if (d1 <= R && d2 > innerR) MOON_CELLS.push({ dx: gx, dy: gy });
    }
  }
}

function drawMoon() {
  const unit = 2;
  noStroke();
  fill(230, 232, 220, 225);
  MOON_CELLS.forEach(p => rect(MOON_X + p.dx * unit, MOON_Y + p.dy * unit, unit, unit));
}

// Static star field -- generated once and never re-randomized (so it
// doesn't flicker), with rejection sampling to stay clear of the legend
// box, the foundation HUD, the cabin silhouette, and the moon.
function buildStars(count) {
  STARS = [];
  const legendZone = { x0: 8, y0: 6, x1: 198, y1: 54 };
  const hudZone    = { x0: canvasW - 160, y0: 8, x1: canvasW - 10, y1: 38 };
  const cabinZone  = { x0: canvasW / 2 - 40, y0: 0, x1: canvasW / 2 + 40, y1: grassY };

  let attempts = 0;
  while (STARS.length < count && attempts < 400) {
    attempts++;
    const x = random(4, canvasW - 4);
    const y = random(2, grassY - 4);
    const inZone = (z) => x >= z.x0 && x <= z.x1 && y >= z.y0 && y <= z.y1;
    if (inZone(legendZone) || inZone(hudZone) || inZone(cabinZone)) continue;
    if (dist(x, y, MOON_X, MOON_Y) < 14) continue;
    STARS.push({ x, y, size: random() < 0.7 ? 1 : 2, alpha: random(45, 120) });
  }
}

function drawStars() {
  noStroke();
  STARS.forEach(s => { fill(210, 216, 235, s.alpha); rect(s.x, s.y, s.size, s.size); });
}

function drawGrassStrip() {
  noStroke();
  fill(COL_GRASS);
  rect(0, grassY, canvasW, GRASS_HEIGHT);
  fill(46, 66, 30);
  GRASS_TUFTS.forEach(x => rect(x, grassY + GRASS_HEIGHT - 4, 2, 4));
}

// ---------------------------------------------------------------------------
// CABIN LOGIC: foundation-zone integrity
// ---------------------------------------------------------------------------

// Called once in setup: defines the column span under the cabin and
// collects the indices of every cell in the "foundation zone" (cabin's
// width x top FOUNDATION_ROWS rows of soil) once, so the per-frame health
// check only ever has to .forEach() a small fixed list.
function computeFoundationZone() {
  const bx = canvasW / 2 - CABIN_W / 2;
  foundationColStart = constrain(floor(bx / CELL_SIZE), 0, cols - 1);
  foundationColEnd   = constrain(ceil((bx + CABIN_W) / CELL_SIZE), 0, cols - 1);
  FOUNDATION_INDICES = [];
  for (let r = 0; r < FOUNDATION_ROWS && r < rows; r++) {
    for (let c = foundationColStart; c <= foundationColEnd; c++) {
      FOUNDATION_INDICES.push(idx(c, r));
    }
  }
}

// Foundation Health % = (remaining solid soil / total zone area) * 100
function computeFoundationHealth() {
  if (FOUNDATION_INDICES.length === 0) return 100;
  let dug = 0;
  FOUNDATION_INDICES.forEach(i => { if (intensityGrid[i] > 0) dug++; });
  const solidRatio = 1 - dug / FOUNDATION_INDICES.length;
  return constrain(solidRatio * 100, 0, 100);
}

// Cabin geometry, expressed as simple pixel-art fragments relative to a
// given top-left anchor -- reused both for the intact drawing and (broken
// apart) for the collapse animation.
function cabinParts(bx, topY) {
  return [
    { type: 'rect', x: bx, y: topY + 16, w: CABIN_W, h: CABIN_H - 16, c: COL_WOOD },
    { type: 'tri',  pts: [[bx - 4, topY + 16], [bx + CABIN_W / 2, topY - 8], [bx + CABIN_W + 4, topY + 16]], c: COL_ROOF },
    { type: 'rect', x: bx + CABIN_W / 2 - 6, y: topY + CABIN_H - 16, w: 12, h: 16, c: COL_WOOD_DARK },
    { type: 'rect', x: bx + 8, y: topY + 22, w: 8, h: 8, c: COL_WINDOW },
    { type: 'rect', x: bx + CABIN_W - 16, y: topY + 22, w: 8, h: 8, c: COL_WINDOW },
    { type: 'rect', x: bx + CABIN_W - 18, y: topY - 16, w: 6, h: 10, c: COL_CHIMNEY },
  ];
}

function drawCabinIntact(shakeX) {
  const topY = grassY - CABIN_H;
  const bx = canvasW / 2 - CABIN_W / 2 + shakeX;
  cabinParts(bx, topY).forEach(p => {
    noStroke();
    fill(p.c);
    if (p.type === 'rect') rect(p.x, p.y, p.w, p.h);
    else triangle(p.pts[0][0], p.pts[0][1], p.pts[1][0], p.pts[1][1], p.pts[2][0], p.pts[2][1]);
  });
}

// Phase 2: subtle side-to-side shake, amplitude scaling up as health drops
// from the warning threshold toward the collapse threshold.
function shakeOffsetForHealth(h) {
  if (h >= HEALTH_WARNING) return 0;
  const t = constrain(map(h, HEALTH_COLLAPSE, HEALTH_WARNING, 1, 0), 0, 1);
  const amt = t * SHAKE_MAX;
  const n = noise(9999, frameCount * 0.3);
  return map(n, 0, 1, -amt, amt);
}

// Phase 2: dust particles falling from the floorboards.
function spawnDust() {
  if (dustParticles.length >= MAX_DUST) return;
  const bx = canvasW / 2 - CABIN_W / 2;
  dustParticles.push({
    x: bx + random(6, CABIN_W - 6),
    y: grassY - random(0, 6),
    vy: random(0.4, 1.0),
    vx: random(-0.3, 0.3),
    life: 255,
  });
}

function updateDust() {
  dustParticles.forEach(p => { p.x += p.vx; p.y += p.vy; p.life -= 4; });
  dustParticles = dustParticles.filter(p => p.life > 0 && p.y < gridTopY + 20);
}

function drawDust() {
  noStroke();
  dustParticles.forEach(p => { fill(93, 63, 41, p.life); rect(p.x, p.y, 2, 2); });
}

// Phase 3: break the cabin into falling, tumbling fragments.
function triggerCollapse() {
  const topY = grassY - CABIN_H;
  const bx = canvasW / 2 - CABIN_W / 2;
  collapsePieces = cabinParts(bx, topY).map(p => {
    let cx, cy;
    if (p.type === 'rect') { cx = p.x + p.w / 2; cy = p.y + p.h / 2; }
    else { cx = (p.pts[0][0] + p.pts[1][0] + p.pts[2][0]) / 3; cy = (p.pts[0][1] + p.pts[1][1] + p.pts[2][1]) / 3; }
    return { ...p, cx, cy, vx: random(-1.2, 1.2), vy: random(-1.5, -0.3), angle: 0, vAngle: random(-0.12, 0.12) };
  });
  cabinState = 'collapsing';
  collapseTimer = 0;
}

function updateCollapsePieces() {
  collapsePieces.forEach(p => {
    p.vy += 0.28; // gravity
    p.cx += p.vx;
    p.cy += p.vy;
    p.angle += p.vAngle;
  });
  collapseTimer++;
  if (collapseTimer > COLLAPSE_DURATION_FRAMES) {
    cabinState = 'collapsed';
    collapsePieces = [];
  }
}

function drawCollapsePieces() {
  collapsePieces.forEach(p => {
    push();
    translate(p.cx, p.cy);
    rotate(p.angle);
    noStroke();
    fill(p.c);
    if (p.type === 'rect') {
      rect(-p.w / 2, -p.h / 2, p.w, p.h);
    } else {
      triangle(-9, 7, 0, -11, 9, 7);
    }
    pop();
  });
}

// Drives the three collapse phases every simulated frame.
function updateFoundationAndCabin() {
  foundationHealth = computeFoundationHealth();
  updateDust();

  if (cabinState === 'intact' || cabinState === 'warning') {
    if (foundationHealth < HEALTH_COLLAPSE) {
      triggerCollapse(); // Phase 3
    } else if (foundationHealth < HEALTH_WARNING) {
      cabinState = 'warning'; // Phase 2
      if (random() < DUST_SPAWN_CHANCE) spawnDust();
    } else {
      cabinState = 'intact'; // Phase 1
    }
  } else if (cabinState === 'collapsing') {
    updateCollapsePieces();
  }
  // 'collapsed' persists until Reset Soil is pressed -- track how long it's
  // been sitting there so draw() can give the player a moment to see it.
  if (cabinState === 'collapsed') collapsedHoldTimer++;
}

function drawFoundationHUD() {
  const hudW = 150, hudH = 30;
  const hx = canvasW - hudW - 10, hy = 8;
  noStroke();
  fill(20, 16, 14, 210);
  rect(hx, hy, hudW, hudH, 4);

  const pct = foundationHealth;
  const barColor = pct >= HEALTH_WARNING ? color(120, 190, 110)
                  : pct >= HEALTH_COLLAPSE ? color(224, 178, 74)
                  : color(214, 80, 64);

  fill(230, 220, 205);
  textFont('monospace');
  textSize(10);
  textAlign(LEFT, TOP);
  text('FOUNDATION', hx + 8, hy + 4);
  textAlign(RIGHT, TOP);
  text(floor(pct) + '%', hx + hudW - 8, hy + 4);

  noStroke();
  fill(50, 40, 34);
  rect(hx + 8, hy + 16, hudW - 16, 8);
  fill(barColor);
  rect(hx + 8, hy + 16, (hudW - 16) * (pct / 100), 8);
}

function drawCollapseOverlay() {
  if (cabinState !== 'collapsing' && cabinState !== 'collapsed') return;
  const flick = 160 + 60 * sin(frameCount * 0.15);
  noStroke();
  fill(10, 8, 8, 190);
  rect(0, grassY - 16, canvasW, 16);
  fill(214, 70, 58, flick);
  textFont('monospace');
  textSize(11);
  textAlign(CENTER, CENTER);
  text('SURFACE STRUCTURAL COLLAPSE \u2014 OVER-EXCAVATION DETECTED', canvasW / 2, grassY - 8);
}

// Small always-on legend, tucked in the top-left corner -- sized to stay
// clear of both the centered cabin and the top-right foundation HUD.
function drawLegend() {
  const lx = 8, ly = 6, lw = 190, lh = 48, pad = 8;

  noStroke();
  fill(20, 16, 14, 190);
  rect(lx, ly, lw, lh, 3);

  noFill();
  stroke(196, 148, 76, 110);
  strokeWeight(1);
  rect(lx, ly, lw, lh, 3);

  noStroke();
  fill(230, 220, 205, 230);
  textFont('monospace');
  textSize(9);
  textAlign(LEFT, TOP);
  text('\u25CF Grey Dots: Rabbit Agents', lx + pad, ly + pad - 2);
  text('\u2591 Hollow Paths: Emergent Tunnels', lx + pad, ly + pad + 10);
  fill(200, 188, 168, 210);
  text('Tip: Click dirt to spawn a rabbit.', lx + pad, ly + pad + 22);
}

// Repaints the whole cabin scene (sky, grass, dust, cabin/rubble, HUD) every
// frame -- unlike the soil grid, this small area must be redrawn each frame
// to animate the shake/dust/collapse.
function drawCabinScene() {
  drawSky();
  drawStars();
  drawMoon();
  drawGrassStrip();
  drawDust();
  if (cabinState === 'intact') drawCabinIntact(0);
  else if (cabinState === 'warning') drawCabinIntact(shakeOffsetForHealth(foundationHealth));
  else if (cabinState === 'collapsing') drawCollapsePieces();
  drawFoundationHUD();
  drawCollapseOverlay();
  drawLegend();
}

// ---------------------------------------------------------------------------
// 4. AGENT CLASS
// ---------------------------------------------------------------------------
class Agent {
  constructor(x, y, angle, energy) {
    this.x = x;
    this.y = y;
    this.angle = angle;
    this.energy = energy;
    this.alive = true;
    this.noiseSeed = random(10000);
    this.cellIdx = -1;
    this.recentCells = [];
  }

  dig() {
    let { c, r } = toCell(this.x, this.y);
    c = constrain(c, 0, cols - 1);
    r = constrain(r, 0, rows - 1);
    this.cellIdx = idx(c, r);
    if (rockGrid[this.cellIdx]) return;

    intensityGrid[this.cellIdx] = min(intensityGrid[this.cellIdx] + 1.1, INTENSITY_MAX);
    pheromoneGrid[this.cellIdx] = min(pheromoneGrid[this.cellIdx] + 3.5, PHEROMONE_MAX);

    this.recentCells.push(this.cellIdx);
    if (this.recentCells.length > SELF_TRAIL_MEMORY) this.recentCells.shift();

    redrawWithNeighbors(c, r);
  }

  // -------------------------------------------------------------------
  // SWARM LOGIC #1: MERGE INTO EXISTING TUNNEL (stigmergic convergence)
  // Uses the precomputed MERGE_OFFSETS list via .forEach() instead of a
  // raw nested for-loop, since this runs once per agent, every frame.
  // Cells in the agent's own recent trail are excluded -- without that,
  // an agent always finds its own freshest tunnel right behind it and
  // spirals into it forever (the "spring coil" bug).
  // -------------------------------------------------------------------
  senseMergeTarget() {
    const { c, r } = toCell(this.x, this.y);
    let bestVal = -1, bestC = c, bestR = r, found = false;

    MERGE_OFFSETS.forEach(({ dc, dr }) => {
      const cc = c + dc, rr = r + dr;
      if (cc < 0 || cc >= cols || rr < 0 || rr >= rows) return;
      const i = idx(cc, rr);
      if (intensityGrid[i] < MERGE_MIN_INTENSITY) return;
      if (this.recentCells.includes(i)) return;
      if (intensityGrid[i] > bestVal) { bestVal = intensityGrid[i]; bestC = cc; bestR = rr; found = true; }
    });

    if (!found) return null;
    const targetX = bestC * CELL_SIZE + CELL_SIZE / 2;
    const targetY = gridTopY + bestR * CELL_SIZE + CELL_SIZE / 2;
    return atan2(targetY - this.y, targetX - this.x);
  }

  // -------------------------------------------------------------------
  // ORGANIC MOVEMENT VIA A SPATIAL PERLIN FLOW FIELD
  // -------------------------------------------------------------------
  steer() {
    const n = noise(this.x * FLOW_NOISE_SCALE, this.y * FLOW_NOISE_SCALE, frameCount * FLOW_TIME_SCALE);
    const flowAngle = n * TWO_PI * FLOW_ANGLE_SPAN;

    let vx = cos(flowAngle);
    let vy = sin(flowAngle) + GRAVITY_BIAS;

    const dxOut = this.x - canvasW / 2;
    const dyOut = this.y - (gridTopY + 40);
    const distOut = max(1, sqrt(dxOut * dxOut + dyOut * dyOut));
    vx += (dxOut / distOut) * OUTWARD_BIAS;
    vy += (dyOut / distOut) * OUTWARD_BIAS;

    let targetAngle = atan2(vy, vx);

    const mergeAngle = this.senseMergeTarget();
    if (mergeAngle !== null && random() < MERGE_CHANCE) {
      targetAngle = lerpAngle(targetAngle, mergeAngle, MERGE_PULL_STRENGTH);
    }

    this.angle = lerpAngle(this.angle, targetAngle, TURN_SMOOTH);
  }

  move() {
    let nx = this.x + cos(this.angle) * BASE_SPEED;
    let ny = this.y + sin(this.angle) * BASE_SPEED;

    if (nx < 0 || nx >= canvasW) { this.angle = PI - this.angle; nx = constrain(nx, 1, canvasW - 1); }
    if (ny < gridTopY || ny >= gridBottomY) { this.angle = -this.angle; ny = constrain(ny, gridTopY + 1, gridBottomY - 1); }

    const { c, r } = toCell(nx, ny);
    const cc = constrain(c, 0, cols - 1), rr = constrain(r, 0, rows - 1);
    if (rockGrid[idx(cc, rr)]) {
      this.angle += PI + random(-0.6, 0.6);
      this.energy -= ROCK_COLLISION_ENERGY_COST;
      return;
    }
    this.x = nx;
    this.y = ny;
  }

  // -------------------------------------------------------------------
  // SWARM LOGIC #2: CROWD-REPULSION BRANCHING ("into fresh dirt")
  // Uses the precomputed DENSITY_OFFSETS list via .forEach().
  // -------------------------------------------------------------------
  checkBranch(newAgents) {
    const { c, r } = toCell(this.x, this.y);
    let density = 0, sumDX = 0, sumDY = 0;

    DENSITY_OFFSETS.forEach(({ dc, dr }) => {
      const cc = c + dc, rr = r + dr;
      if (cc < 0 || cc >= cols || rr < 0 || rr >= rows) return;
      const cnt = agentCountGrid[idx(cc, rr)];
      density += cnt;
      sumDX += dc * cnt;
      sumDY += dr * cnt;
    });

    if (density >= DENSITY_BRANCH_THRESHOLD &&
        this.energy > BRANCH_ENERGY_COST &&
        agents.length + newAgents.length < MAX_AGENTS &&
        random() < BRANCH_CHANCE) {
      const awayAngle = (sumDX === 0 && sumDY === 0)
        ? random(TWO_PI)
        : atan2(-sumDY, -sumDX) + random(-0.5, 0.5);
      const child = new Agent(this.x, this.y, awayAngle, this.energy * 0.5);
      this.energy *= 0.6;
      newAgents.push(child);
    }
  }

  // -------------------------------------------------------------------
  // SWARM LOGIC #3: PROXIMITY REPRODUCTION (paths crossing in a tunnel)
  // -------------------------------------------------------------------
  checkReproduce(newAgents) {
    if (agentCountGrid[this.cellIdx] >= 2 &&
        this.energy > REPRO_ENERGY_COST &&
        agents.length + newAgents.length < MAX_AGENTS &&
        random() < REPRO_CHANCE) {
      this.energy -= REPRO_ENERGY_COST;
      const child = new Agent(this.x, this.y, random(TWO_PI), this.energy * 0.6);
      newAgents.push(child);
    }
  }

  checkDeath() {
    this.energy -= ENERGY_DECAY_PER_FRAME;
    if (this.energy <= 0 && this.alive) {
      this.alive = false;
      noStroke();
      fill(COL_STONE);
      ellipse(this.x, this.y, CELL_SIZE * 1.6);
      fill(red(COL_STONE) + 40, green(COL_STONE) + 40, blue(COL_STONE) + 40, 160);
      ellipse(this.x, this.y, CELL_SIZE * 0.7);
    }
  }

  drawHead() {
    push();
    noStroke();
    fill(COL_HEAD);
    ellipse(this.x, this.y, CELL_SIZE * 1.2);
    pop();
  }
}

// ---------------------------------------------------------------------------
// 5. SPAWNING HELPERS
// ---------------------------------------------------------------------------
function spawnAgentAt(x, y, biasDownward) {
  if (agents.length >= MAX_AGENTS) return;
  const angle = biasDownward ? HALF_PI + random(-0.9, 0.9) : random(TWO_PI);
  const a = new Agent(x, y, angle, random(ENERGY_MIN_START, ENERGY_MAX_START));
  agents.push(a);
  a.dig();
}

function addSwarm(n) {
  Array.from({ length: n }).forEach(() => {
    const x = random(canvasW);
    const y = gridTopY + random(0, 24);
    spawnAgentAt(x, y, true);
  });
}

// Runs every frame (for the auto-reset check below), so it uses TypedArray's
// native .forEach() rather than a raw for-loop.
function tunnelCoverage() {
  let dug = 0;
  intensityGrid.forEach(v => { if (v > 0) dug++; });
  return dug / intensityGrid.length;
}

function resetSimulation() {
  agents = [];
  generation++;

  generateSoil();
  startSoilReveal();

  const cx = canvasW / 2;
  for (let i = 0; i < INITIAL_AGENTS; i++) {
    spawnAgentAt(cx + random(-60, 60), gridTopY + random(0, 12), true);
  }

  isRunning = true;

  // CABIN LOGIC: rebuild the intact cabin on every reset.
  cabinState = 'intact';
  foundationHealth = 100;
  dustParticles = [];
  collapsePieces = [];
  collapseTimer = 0;
  collapsedHoldTimer = 0;
}

// ---------------------------------------------------------------------------
// 6. UI -- BOTTOM CONTROL DECK
// ---------------------------------------------------------------------------
function buildButtons() {
  const margin = 20, gap = 18;
  const btnW = (canvasW - margin * 2 - gap * 2) / 3;
  const btnH = PANEL_HEIGHT - 36;
  const y = gridBottomY + 18;
  buttons = [
    { id: 'toggle', x: margin, y, w: btnW, h: btnH },
    { id: 'reset',  x: margin + btnW + gap, y, w: btnW, h: btnH },
    { id: 'swarm',  x: margin + (btnW + gap) * 2, y, w: btnW, h: btnH },
  ];
}

function buttonLabel(id) {
  if (id === 'toggle') return isRunning ? '\u23F8  PAUSE' : '\u25B6  START';
  if (id === 'reset')  return '\u27F2  RESET SOIL';
  if (id === 'swarm')  return '+' + SWARM_BUTTON_COUNT + '  ADD SWARM';
  return '';
}

function drawPanel() {
  noStroke();
  fill(COL_PANEL_BG);
  rect(0, gridBottomY, canvasW, PANEL_HEIGHT);
  fill(COL_PANEL_BORDER);
  rect(0, gridBottomY, canvasW, 3);

  buttons.forEach(b => {
    const hover = mouseX >= b.x && mouseX <= b.x + b.w && mouseY >= b.y && mouseY <= b.y + b.h;
    fill(hover ? COL_BTN_HOVER : COL_BTN);
    stroke(COL_PANEL_BORDER);
    strokeWeight(1.5);
    rect(b.x, b.y, b.w, b.h, 6);
    noStroke();
    fill(COL_BTN_TEXT);
    textAlign(CENTER, CENTER);
    textSize(14);
    textFont('monospace');
    text(buttonLabel(b.id), b.x + b.w / 2, b.y + b.h / 2 + 1);
  });

  fill(COL_BTN_TEXT);
  textAlign(LEFT, CENTER);
  textSize(12);
  text('rabbits: ' + agents.length + '   |   ' + (isRunning ? 'RUNNING' : 'PAUSED'),
       20, gridBottomY + PANEL_HEIGHT - 12);
}

function handleButtonClick(mx, my) {
  let handled = false;
  buttons.forEach(b => {
    if (handled) return;
    if (mx >= b.x && mx <= b.x + b.w && my >= b.y && my <= b.y + b.h) {
      if (b.id === 'toggle') isRunning = !isRunning;
      else if (b.id === 'reset') resetSimulation();
      else if (b.id === 'swarm') addSwarm(SWARM_BUTTON_COUNT);
      handled = true;
    }
  });
  return handled;
}

// ---------------------------------------------------------------------------
// 7. SETUP
// ---------------------------------------------------------------------------
function setup() {
  cols = floor(TARGET_WIDTH / CELL_SIZE);
  rows = floor(TARGET_GRID_HEIGHT / CELL_SIZE);
  gridPixelW = cols * CELL_SIZE;
  gridPixelH = rows * CELL_SIZE;

  canvasW = gridPixelW;
  grassY = CABIN_AREA_H;              // space reserved above the grass for the cabin + HUD
  gridTopY = grassY + GRASS_HEIGHT;
  gridBottomY = gridTopY + gridPixelH;
  canvasH = gridBottomY + PANEL_HEIGHT;

  createCanvas(canvasW, canvasH);
  pixelDensity(1);
  frameRate(60);
  noiseDetail(2, 0.5);

  COL_GRASS         = color(90, 140, 62);
  COL_TUNNEL_DARK    = color(26, 20, 18);
  COL_GLOW_LOW       = color(150, 96, 42);
  COL_GLOW_HIGH      = color(255, 214, 140);
  COL_STONE          = color(112, 100, 90);
  COL_HEAD           = color(255, 244, 214, 100);
  COL_PANEL_BG       = color(31, 24, 19);
  COL_PANEL_BORDER   = color(196, 148, 76);
  COL_BTN            = color(52, 40, 32);
  COL_BTN_HOVER      = color(78, 58, 40);
  COL_BTN_TEXT       = color(238, 220, 195);

  // CABIN LOGIC: palette
  COL_SKY            = color(16, 15, 20);
  COL_WOOD           = color(120, 82, 48);
  COL_WOOD_DARK      = color(74, 48, 28);
  COL_ROOF           = color(150, 58, 44);
  COL_WINDOW         = color(255, 214, 120);
  COL_CHIMNEY        = color(120, 116, 112);
  COL_DUST           = color(93, 63, 41);

  generateSoil();
  background(24, 18, 14);
  startSoilReveal();
  buildButtons();
  buildGrassTufts();
  computeFoundationZone();

  MOON_X = canvasW - 230;
  MOON_Y = 16;
  buildMoonBitmap();
  buildStars(16);

  const cx = canvasW / 2;
  for (let i = 0; i < INITIAL_AGENTS; i++) {
    spawnAgentAt(cx + random(-60, 60), gridTopY + random(0, 12), true);
  }
}

// ---------------------------------------------------------------------------
// 8. MAIN LOOP
// ---------------------------------------------------------------------------
function draw() {
  drawCabinScene(); // always redrawn -- animates independently of the soil

  if (!soilFullyDrawn) stepSoilReveal();

  if (isRunning && soilFullyDrawn) {
    agentCountGrid.fill(0);
    agents.forEach(a => {
      if (!a.alive) return;
      const { c, r } = toCell(a.x, a.y);
      const cc = constrain(c, 0, cols - 1), rr = constrain(r, 0, rows - 1);
      agentCountGrid[idx(cc, rr)]++;
    });

    const newAgents = [];
    agents.forEach(a => {
      if (!a.alive) return;
      a.dig();
      a.checkBranch(newAgents);
      a.checkReproduce(newAgents);
      a.steer();
      a.move();
      a.checkDeath();
      if (a.alive) a.drawHead();
    });
    newAgents.forEach(child => {
      if (agents.length < MAX_AGENTS) agents.push(child);
    });
    agents = agents.filter(a => a.alive);

    pheromoneGrid.forEach((v, i) => { pheromoneGrid[i] = v * PHEROMONE_DECAY; });

    // CABIN LOGIC: check foundation integrity and advance shake/dust/collapse
    updateFoundationAndCabin();
  }

  drawPanel();

  if (inGridArea(mouseY)) cursor(CROSS);
  else {
    let overBtn = false;
    buttons.forEach(b => {
      if (mouseX >= b.x && mouseX <= b.x + b.w && mouseY >= b.y && mouseY <= b.y + b.h) overBtn = true;
    });
    cursor(overBtn ? HAND : ARROW);
  }

  if (isRunning && soilFullyDrawn) {
    const cabinFullyCollapsedAndHeld =
      cabinState === 'collapsed' && collapsedHoldTimer > COLLAPSED_HOLD_SECONDS * 60;
    const soilNearlyGone = tunnelCoverage() > MAX_TUNNEL_COVERAGE;

    if (cabinFullyCollapsedAndHeld || soilNearlyGone) {
      resetSimulation();
    }
  }
}

// ---------------------------------------------------------------------------
// 9. USER INTERACTION
// ---------------------------------------------------------------------------
function mousePressed() {
  const now = millis();
  if (now - lastClickMs < CLICK_DEBOUNCE_MS) return;
  lastClickMs = now;

  if (inGridArea(mouseY)) {
    spawnAgentAt(mouseX, mouseY, true);
  } else if (mouseY >= gridBottomY) {
    handleButtonClick(mouseX, mouseY);
  }
}

function keyPressed() {
  if (key === 's' || key === 'S') saveCanvas('subterranean-swarm', 'png');
}
