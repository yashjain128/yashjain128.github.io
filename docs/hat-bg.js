/*
 * hat-bg.js — animated aperiodic background built from the "hat" einstein
 * monotile (Smith, Myers, Kaplan, Goodman-Strauss, 2023).
 *
 * The tiling is generated mathematically at runtime via the H/T/P/F metatile
 * substitution system; nothing is pre-rendered. Because supertiles share
 * their children (the structure is a DAG, not a tree), each extra level costs
 * almost no memory, so the pattern can drift forever: whenever the camera
 * approaches the edge of the current supertile, one more substitution level
 * is applied and the view is re-anchored so the visible tiles never move.
 *
 * Hat outline, metatile geometry and substitution rules adapted from
 * "hatviz" by Craig S. Kaplan — https://github.com/isohedral/hatviz
 * (BSD 3-Clause License, Copyright (c) 2023 Craig S. Kaplan).
 */
(function () {
'use strict';

/* ---------- tunables ---------- */
const UNIT = 40;              // px per outline unit; a hat is ~3*UNIT wide
const SPEED_X = 2000 / 150;   // drift px/s — same velocity as the old CSS grid
const SPEED_Y = 2000 / 150;
const PAD = 400;              // off-screen margin consumed between repaints
const STROKE = 'rgba(68, 68, 68, 0.18)';
const LINE_W = 1;
const CULL_MARGIN = 3 * UNIT; // hats bulge past their metatile outline a bit
const FLASH_ALPHA = 0.3;      // grey level of a clicked tile
const FLASH_MS = 2500;        // how long a clicked tile takes to fade back

// The hierarchy is anchored at a seed that sits at a "corner" of every
// supertile, so a fixed wedge of directions (up-left of the seed) is never
// covered no matter how many levels are built. We therefore keep the seed
// off-screen to the up-left and drift the camera down-right, deeper into
// the always-covered quadrant.
//
// Built once at init to a fixed depth: level 18 spans ~2.7M units
// (~80M px) from the seed — weeks of continuous drift — and is deep
// enough that transient interior pinholes (which close ~3 levels after
// they appear) are all filled within the reachable corridor. Because
// supertiles share children (a DAG), this costs O(level) memory and
// microseconds of startup time.
const INIT_LEVEL = 18;
const SEED_MARGIN = 200;      // px the seed sits beyond the canvas corner

/* ---------- affine geometry (from hatviz geometry.js) ---------- */
const r3 = 1.7320508075688772;
const hr3 = 0.8660254037844386;
const ident = [1, 0, 0, 0, 1, 0];

function pt(x, y) { return { x: x, y: y }; }
function hexPt(x, y) { return pt(x + 0.5 * y, hr3 * y); }

function inv(T) {
	const det = T[0] * T[4] - T[1] * T[3];
	return [T[4] / det, -T[1] / det, (T[1] * T[5] - T[2] * T[4]) / det,
		-T[3] / det, T[0] / det, (T[2] * T[3] - T[0] * T[5]) / det];
}

function mul(A, B) {
	return [A[0] * B[0] + A[1] * B[3],
		A[0] * B[1] + A[1] * B[4],
		A[0] * B[2] + A[1] * B[5] + A[2],
		A[3] * B[0] + A[4] * B[3],
		A[3] * B[1] + A[4] * B[4],
		A[3] * B[2] + A[4] * B[5] + A[5]];
}

function padd(p, q) { return pt(p.x + q.x, p.y + q.y); }
function psub(p, q) { return pt(p.x - q.x, p.y - q.y); }

function trot(ang) {
	const c = Math.cos(ang), s = Math.sin(ang);
	return [c, -s, 0, s, c, 0];
}

function ttrans(tx, ty) { return [1, 0, tx, 0, 1, ty]; }

function rotAbout(p, ang) {
	return mul(ttrans(p.x, p.y), mul(trot(ang), ttrans(-p.x, -p.y)));
}

function transPt(M, P) {
	return pt(M[0] * P.x + M[1] * P.y + M[2], M[3] * P.x + M[4] * P.y + M[5]);
}

// Match unit interval to segment p->q, then two segments to each other.
function matchSeg(p, q) {
	return [q.x - p.x, p.y - q.y, p.x, q.y - p.y, q.x - p.x, p.y];
}
function matchTwo(p1, q1, p2, q2) {
	return mul(matchSeg(p2, q2), inv(matchSeg(p1, q1)));
}

function intersect(p1, q1, p2, q2) {
	const d = (q2.y - p2.y) * (q1.x - p1.x) - (q2.x - p2.x) * (q1.y - p1.y);
	const uA = ((q2.x - p2.x) * (p1.y - p2.y) - (q2.y - p2.y) * (p1.x - p2.x)) / d;
	return pt(p1.x + uA * (q1.x - p1.x), p1.y + uA * (q1.y - p1.y));
}

/* ---------- the hat and the H/T/P/F substitution system ---------- */
const hat_outline = [
	hexPt(0, 0), hexPt(-1, -1), hexPt(0, -2), hexPt(2, -2),
	hexPt(2, -1), hexPt(4, -2), hexPt(5, -1), hexPt(4, 0),
	hexPt(3, 0), hexPt(2, 2), hexPt(0, 3), hexPt(0, 2),
	hexPt(-1, 2)];

function HatTile(label) {
	this.label = label;   // 'H1' marks the reflected hat
}

function MetaTile(shape, width) {
	this.shape = shape;
	this.width = width;
	this.children = [];
}

MetaTile.prototype.addChild = function (T, geom) {
	this.children.push({ T: T, geom: geom });
};

MetaTile.prototype.evalChild = function (n, i) {
	return transPt(this.children[n].T, this.children[n].geom.shape[i]);
};

MetaTile.prototype.recentre = function () {
	let cx = 0, cy = 0;
	for (const p of this.shape) { cx += p.x; cy += p.y; }
	cx /= this.shape.length;
	cy /= this.shape.length;
	const tr = pt(-cx, -cy);
	for (let idx = 0; idx < this.shape.length; ++idx) {
		this.shape[idx] = padd(this.shape[idx], tr);
	}
	const M = ttrans(-cx, -cy);
	for (const ch of this.children) {
		ch.T = mul(M, ch.T);
	}
};

const H1_hat = new HatTile('H1');
const H_hat = new HatTile('H');
const T_hat = new HatTile('T');
const P_hat = new HatTile('P');
const F_hat = new HatTile('F');

const H_init = (function () {
	const H_outline = [
		pt(0, 0), pt(4, 0), pt(4.5, hr3),
		pt(2.5, 5 * hr3), pt(1.5, 5 * hr3), pt(-0.5, hr3)];
	const meta = new MetaTile(H_outline, 2);

	meta.addChild(
		matchTwo(hat_outline[5], hat_outline[7], H_outline[5], H_outline[0]),
		H_hat);
	meta.addChild(
		matchTwo(hat_outline[9], hat_outline[11], H_outline[1], H_outline[2]),
		H_hat);
	meta.addChild(
		matchTwo(hat_outline[5], hat_outline[7], H_outline[3], H_outline[4]),
		H_hat);
	meta.addChild(
		mul(ttrans(2.5, hr3),
			mul([-0.5, -hr3, 0, hr3, -0.5, 0],
				[0.5, 0, 0, 0, -0.5, 0])),
		H1_hat);

	return meta;
}());

const T_init = (function () {
	const T_outline = [pt(0, 0), pt(3, 0), pt(1.5, 3 * hr3)];
	const meta = new MetaTile(T_outline, 2);
	meta.addChild([0.5, 0, 0.5, 0, 0.5, hr3], T_hat);
	return meta;
}());

const P_init = (function () {
	const P_outline = [
		pt(0, 0), pt(4, 0), pt(3, 2 * hr3), pt(-1, 2 * hr3)];
	const meta = new MetaTile(P_outline, 2);
	meta.addChild([0.5, 0, 1.5, 0, 0.5, hr3], P_hat);
	meta.addChild(
		mul(ttrans(0, 2 * hr3),
			mul([0.5, hr3, 0, -hr3, 0.5, 0],
				[0.5, 0, 0, 0, 0.5, 0])),
		P_hat);
	return meta;
}());

const F_init = (function () {
	const F_outline = [
		pt(0, 0), pt(3, 0), pt(3.5, hr3), pt(3, 2 * hr3), pt(-1, 2 * hr3)];
	const meta = new MetaTile(F_outline, 2);
	meta.addChild([0.5, 0, 1.5, 0, 0.5, hr3], F_hat);
	meta.addChild(
		mul(ttrans(0, 2 * hr3),
			mul([0.5, hr3, 0, -hr3, 0.5, 0],
				[0.5, 0, 0, 0, 0.5, 0])),
		F_hat);
	return meta;
}());

// One generation of the substitution: assemble a patch of 29 metatiles.
function constructPatch(H, T, P, F) {
	const rules = [
		['H'],
		[0, 0, 'P', 2], [1, 0, 'H', 2], [2, 0, 'P', 2], [3, 0, 'H', 2],
		[4, 4, 'P', 2], [0, 4, 'F', 3], [2, 4, 'F', 3],
		[4, 1, 3, 2, 'F', 0],
		[8, 3, 'H', 0], [9, 2, 'P', 0], [10, 2, 'H', 0], [11, 4, 'P', 2],
		[12, 0, 'H', 2], [13, 0, 'F', 3], [14, 2, 'F', 1], [15, 3, 'H', 4],
		[8, 2, 'F', 1],
		[17, 3, 'H', 0], [18, 2, 'P', 0], [19, 2, 'H', 2], [20, 4, 'F', 3],
		[20, 0, 'P', 2], [22, 0, 'H', 2], [23, 4, 'F', 3], [23, 0, 'F', 3],
		[16, 0, 'P', 2],
		[9, 4, 0, 2, 'T', 2],
		[4, 0, 'F', 3]];

	const ret = new MetaTile([], H.width);
	const shapes = { 'H': H, 'T': T, 'P': P, 'F': F };

	for (const r of rules) {
		if (r.length === 1) {
			ret.addChild(ident, shapes[r[0]]);
		} else if (r.length === 4) {
			const poly = ret.children[r[0]].geom.shape;
			const T0 = ret.children[r[0]].T;
			const P0 = transPt(T0, poly[(r[1] + 1) % poly.length]);
			const Q0 = transPt(T0, poly[r[1]]);
			const nshp = shapes[r[2]];
			const npoly = nshp.shape;
			ret.addChild(
				matchTwo(npoly[r[3]], npoly[(r[3] + 1) % npoly.length], P0, Q0),
				nshp);
		} else {
			const chP = ret.children[r[0]];
			const chQ = ret.children[r[2]];
			const P0 = transPt(chQ.T, chQ.geom.shape[r[3]]);
			const Q0 = transPt(chP.T, chP.geom.shape[r[1]]);
			const nshp = shapes[r[4]];
			const npoly = nshp.shape;
			ret.addChild(
				matchTwo(npoly[r[5]], npoly[(r[5] + 1) % npoly.length], P0, Q0),
				nshp);
		}
	}
	return ret;
}

// Extract the four next-generation supertiles from a patch.
function constructMetatiles(patch) {
	const bps1 = patch.evalChild(8, 2);
	const bps2 = patch.evalChild(21, 2);
	const rbps = transPt(rotAbout(bps1, -2.0 * Math.PI / 3.0), bps2);

	const p72 = patch.evalChild(7, 2);
	const p252 = patch.evalChild(25, 2);

	const llc = intersect(bps1, rbps, patch.evalChild(6, 2), p72);
	let w = psub(patch.evalChild(6, 2), llc);

	const new_H_outline = [llc, bps1];
	w = transPt(trot(-Math.PI / 3), w);
	new_H_outline.push(padd(new_H_outline[1], w));
	new_H_outline.push(patch.evalChild(14, 2));
	w = transPt(trot(-Math.PI / 3), w);
	new_H_outline.push(psub(new_H_outline[3], w));
	new_H_outline.push(patch.evalChild(6, 2));

	const new_H = new MetaTile(new_H_outline, patch.width * 2);
	for (const ch of [0, 9, 16, 27, 26, 6, 1, 8, 10, 15]) {
		new_H.addChild(patch.children[ch].T, patch.children[ch].geom);
	}

	const new_P_outline = [p72, padd(p72, psub(bps1, llc)), bps1, llc];
	const new_P = new MetaTile(new_P_outline, patch.width * 2);
	for (const ch of [7, 2, 3, 4, 28]) {
		new_P.addChild(patch.children[ch].T, patch.children[ch].geom);
	}

	const new_F_outline = [
		bps2, patch.evalChild(24, 2), patch.evalChild(25, 0),
		p252, padd(p252, psub(llc, bps1))];
	const new_F = new MetaTile(new_F_outline, patch.width * 2);
	for (const ch of [21, 20, 22, 23, 24, 25]) {
		new_F.addChild(patch.children[ch].T, patch.children[ch].geom);
	}

	const AAA = new_H_outline[2];
	const BBB = padd(new_H_outline[1],
		psub(new_H_outline[4], new_H_outline[5]));
	const CCC = transPt(rotAbout(BBB, -Math.PI / 3), AAA);
	const new_T_outline = [BBB, CCC, AAA];
	const new_T = new MetaTile(new_T_outline, patch.width * 2);
	new_T.addChild(patch.children[11].T, patch.children[11].geom);

	new_H.recentre();
	new_P.recentre();
	new_F.recentre();
	new_T.recentre();

	return [new_H, new_T, new_P, new_F];
}

/* ---------- background engine ---------- */
let tiles = [H_init, T_init, P_init, F_init];
let level = 1;
let world = ident;      // maps the top supertile's frame back to the seed frame

// A lone H supertile's hat-coverage is a ragged blob with deep boundary
// indentations, so we render the full 29-supertile patch around it:
// the surrounding pieces fill the fringes along the drift corridor.
let topPatch = constructPatch(tiles[0], tiles[1], tiles[2], tiles[3]);

let canvas, ctx, dpr;
let cssW = 0, cssH = 0; // canvas CSS size (viewport + 2*PAD)
let rx = 0, ry = 0;     // drift offset at last repaint
let strokePath;

let fx, fctx;           // overlay canvas for click flashes
let fxW = 0, fxH = 0;
let flashes = [];       // {poly: pattern-frame vertices, t0: timestamp}
let lastDx = 0, lastDy = 0;

// Grow one substitution level. The previous top-level supertile becomes
// child 0 of the new one at a pure translation C; folding inv(C) into the
// world transform keeps the seed frame fixed.
function substitute() {
	tiles = constructMetatiles(topPatch);
	world = mul(world, inv(tiles[0].children[0].T));
	topPatch = constructPatch(tiles[0], tiles[1], tiles[2], tiles[3]);
	++level;
}

// Seed sits at screen (-PAD-SEED_MARGIN, ..) — i.e. SEED_MARGIN px beyond
// the canvas's top-left corner. rx/ry grow over time, sliding the camera
// down-right in the seed frame, always away from the uncovered wedge.
function drawTransform() {
	return mul(ttrans(-SEED_MARGIN - rx, -SEED_MARGIN - ry),
		mul([UNIT, 0, 0, 0, UNIT, 0], world));
}

// Maps pattern coordinates directly to *viewport* coordinates at drift
// (dx, dy) — the canvas's -PAD offset and CSS translate cancel out of this.
function screenTransform(dx, dy) {
	return mul(ttrans(-SEED_MARGIN - PAD - dx, -SEED_MARGIN - PAD - dy),
		mul([UNIT, 0, 0, 0, UNIT, 0], world));
}

function pointInPoly(p, poly) {
	let inside = false;
	for (let i = 0, j = poly.length - 1; i < poly.length; j = i++) {
		const a = poly[i], b = poly[j];
		if ((a.y > p.y) !== (b.y > p.y) &&
			p.x < (b.x - a.x) * (p.y - a.y) / (b.y - a.y) + a.x) {
			inside = !inside;
		}
	}
	return inside;
}

// Find the hat under a viewport point; returns its pattern-frame polygon.
function hatAt(screenPt) {
	const target = transPt(inv(screenTransform(lastDx, lastDy)), screenPt);
	let found = null;
	(function search(geom, T) {
		if (found) return;
		if (geom instanceof HatTile) {
			const poly = hat_outline.map(function (p) { return transPt(T, p); });
			if (pointInPoly(target, poly)) found = poly;
			return;
		}
		for (const ch of geom.children) {
			if (found) return;
			const Tc = mul(T, ch.T);
			const shape = (ch.geom instanceof HatTile) ? hat_outline : ch.geom.shape;
			let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
			for (const p of shape) {
				const tp = transPt(Tc, p);
				if (tp.x < minX) minX = tp.x;
				if (tp.x > maxX) maxX = tp.x;
				if (tp.y < minY) minY = tp.y;
				if (tp.y > maxY) maxY = tp.y;
			}
			const m = 3 + 0.25 * Math.max(maxX - minX, maxY - minY);
			if (target.x < minX - m || target.x > maxX + m ||
				target.y < minY - m || target.y > maxY + m) {
				continue;
			}
			search(ch.geom, Tc);
		}
	})(topPatch, ident);
	return found;
}

function drawFlashes(now) {
	fctx.setTransform(dpr, 0, 0, dpr, 0, 0);
	fctx.clearRect(0, 0, fxW, fxH);
	if (!flashes.length) return;
	const T = screenTransform(lastDx, lastDy);
	for (let i = flashes.length - 1; i >= 0; --i) {
		const u = (now - flashes[i].t0) / FLASH_MS;
		if (u >= 1) { flashes.splice(i, 1); continue; }
		fctx.beginPath();
		const poly = flashes[i].poly;
		for (let j = 0; j < poly.length; ++j) {
			const s = transPt(T, poly[j]);
			if (j === 0) fctx.moveTo(s.x, s.y);
			else fctx.lineTo(s.x, s.y);
		}
		fctx.closePath();
		// full grey on click, ease-out fade back to white
		fctx.fillStyle =
			'rgba(68, 68, 68, ' + (FLASH_ALPHA * (1 - u) * (1 - u)) + ')';
		fctx.fill();
	}
}

function addHat(S) {
	const p0 = transPt(S, hat_outline[0]);
	strokePath.moveTo(p0.x, p0.y);
	for (let i = 1; i < hat_outline.length; ++i) {
		const p = transPt(S, hat_outline[i]);
		strokePath.lineTo(p.x, p.y);
	}
	strokePath.closePath();
}

function walk(geom, S) {
	if (geom instanceof HatTile) {
		addHat(S);
		return;
	}
	for (const ch of geom.children) {
		const Sc = mul(S, ch.T);
		if (ch.geom instanceof HatTile) {
			// leaves are cheap; their parent was already culled
			addHat(Sc);
			continue;
		}
		let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
		for (const p of ch.geom.shape) {
			const tp = transPt(Sc, p);
			if (tp.x < minX) minX = tp.x;
			if (tp.x > maxX) maxX = tp.x;
			if (tp.y < minY) minY = tp.y;
			if (tp.y > maxY) maxY = tp.y;
		}
		// fractal boundary: hats can overhang the straight outline by a
		// fraction of the metatile's size, so scale the margin with it
		const m = CULL_MARGIN + 0.25 * Math.max(maxX - minX, maxY - minY);
		if (maxX < -m || minX > cssW + m || maxY < -m || minY > cssH + m) {
			continue;
		}
		walk(ch.geom, Sc);
	}
}

function render() {
	ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
	ctx.clearRect(0, 0, cssW, cssH);
	strokePath = new Path2D();
	walk(topPatch, drawTransform());
	ctx.strokeStyle = STROKE;
	ctx.lineWidth = LINE_W;
	ctx.lineJoin = 'round';
	ctx.stroke(strokePath);
	strokePath = null;
}

function resize() {
	dpr = Math.min(window.devicePixelRatio || 1, 2);
	cssW = window.innerWidth + 2 * PAD;
	cssH = window.innerHeight + 2 * PAD;
	canvas.width = Math.round(cssW * dpr);
	canvas.height = Math.round(cssH * dpr);
	canvas.style.width = cssW + 'px';
	canvas.style.height = cssH + 'px';
	canvas.style.top = -PAD + 'px';
	canvas.style.left = -PAD + 'px';
	fxW = window.innerWidth;
	fxH = window.innerHeight;
	fx.width = Math.round(fxW * dpr);
	fx.height = Math.round(fxH * dpr);
	fx.style.width = fxW + 'px';
	fx.style.height = fxH + 'px';
	render();
}

function start() {
	canvas = document.getElementById('hat-bg');
	if (!canvas || !canvas.getContext) return;
	ctx = canvas.getContext('2d');

	// overlay canvas for click flashes, stacked just above the tiling
	fx = document.createElement('canvas');
	fx.style.cssText =
		'position:fixed;top:0;left:0;z-index:-1;pointer-events:none;';
	canvas.parentNode.insertBefore(fx, canvas.nextSibling);
	fctx = fx.getContext('2d');

	while (level < INIT_LEVEL) substitute();

	resize();

	let resizeTimer = null;
	window.addEventListener('resize', function () {
		clearTimeout(resizeTimer);
		resizeTimer = setTimeout(resize, 150);
	});

	const motion = !(window.matchMedia &&
		window.matchMedia('(prefers-reduced-motion: reduce)').matches);

	let t0 = null;
	let looping = false;
	function frame(t) {
		if (t0 === null) t0 = t;
		const el = (t - t0) / 1000;
		if (motion) {
			lastDx = SPEED_X * el;
			lastDy = SPEED_Y * el;
			if (lastDx - rx > PAD - 64 || lastDy - ry > PAD - 64) {
				rx = lastDx;
				ry = lastDy;
				render();
			}
			canvas.style.transform = 'translate3d(' +
				(rx - lastDx) + 'px,' + (ry - lastDy) + 'px,0)';
		}
		drawFlashes(t);
		if (motion || flashes.length) {
			requestAnimationFrame(frame);
		} else {
			looping = false;
		}
	}
	function startLoop() {
		if (!looping) {
			looping = true;
			requestAnimationFrame(frame);
		}
	}

	document.addEventListener('click', function (e) {
		if (e.target && e.target.closest && e.target.closest('a')) return;
		const poly = hatAt(pt(e.clientX, e.clientY));
		if (poly) {
			flashes.push({ poly: poly, t0: performance.now() });
			startLoop();
		}
	});

	if (motion) startLoop();
}

if (typeof module !== 'undefined' && module.exports) {
	// test hook (Node) — not used in the browser
	module.exports = {
		pt: pt, hexPt: hexPt, inv: inv, mul: mul, transPt: transPt,
		ttrans: ttrans, ident: ident, hat_outline: hat_outline,
		HatTile: HatTile, MetaTile: MetaTile,
		H_init: H_init, T_init: T_init, P_init: P_init, F_init: F_init,
		constructPatch: constructPatch,
		constructMetatiles: constructMetatiles
	};
} else if (document.readyState === 'loading') {
	document.addEventListener('DOMContentLoaded', start);
} else {
	start();
}

}());
