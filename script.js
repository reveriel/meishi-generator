/* =====================================================================
   名刺作成ツール — script.js
   純静的・依存ゼロ。名刺を SVG（実寸mm）で描画し、印刷シートとPNG保存を生成する。
   ===================================================================== */
(function () {
  'use strict';

  /* ===================================================================
     0. 汎用ヘルパー
     =================================================================== */

  function byId(id) { return document.getElementById(id); }
  function qsa(sel, root) { return Array.prototype.slice.call((root || document).querySelectorAll(sel)); }

  function esc(s) {
    return String(s == null ? '' : s)
      .replace(/&/g, '&amp;')
      .replace(/</g, '&lt;')
      .replace(/>/g, '&gt;')
      .replace(/"/g, '&quot;')
      .replace(/'/g, '&#39;');
  }

  function trim(s) { return String(s == null ? '' : s).replace(/^\s+|\s+$/g, ''); }

  /* 色を白と混ぜて淡くする（amt: 0=元の色, 1=白） */
  function lighten(hex, amt) {
    var m = /^#?([0-9a-f]{6})$/i.exec(String(hex));
    if (!m) return hex;
    var n = parseInt(m[1], 16);
    var r = (n >> 16) & 255, g = (n >> 8) & 255, b = n & 255;
    function mix(c) { return Math.round(c + (255 - c) * amt); }
    function h2(c) { var s = mix(c).toString(16); return s.length < 2 ? '0' + s : s; }
    return '#' + h2(r) + h2(g) + h2(b);
  }

  /* 文字の幅を em 単位で概算（全角=1.0 / 半角=0.52） */
  function charW(ch) {
    var c = ch.codePointAt(0);
    if (c < 0x1100) return 0.52;
    if (
      (c >= 0x1100 && c <= 0x115F) ||
      (c >= 0x2E80 && c <= 0xA4CF) ||
      (c >= 0xAC00 && c <= 0xD7A3) ||
      (c >= 0xF900 && c <= 0xFAFF) ||
      (c >= 0xFE30 && c <= 0xFE4F) ||
      (c >= 0xFF00 && c <= 0xFF60) ||
      (c >= 0xFFE0 && c <= 0xFFE6) ||
      (c >= 0x2460 && c <= 0x24FF) ||
      (c >= 0x25A0 && c <= 0x25FF) ||
      (c >= 0x2600 && c <= 0x27BF) ||
      (c >= 0x1F300 && c <= 0x1FAFF)
    ) return 1;
    return 0.52;
  }

  function textWidthEm(s) {
    var w = 0;
    for (var i = 0; i < s.length; i++) w += charW(s[i]);
    return w;
  }

  /* maxEm（em単位の幅）で折り返す。maxLines で行数を制限し、超過分は末尾省略 */
  function wrapText(s, maxEm, maxLines) {
    var lines = [], cur = '', w = 0, i, ch, cw;
    for (i = 0; i < s.length; i++) {
      ch = s[i];
      if (ch === '\n') { lines.push(cur); cur = ''; w = 0; continue; }
      cw = charW(ch);
      if (w + cw > maxEm && cur !== '') { lines.push(cur); cur = ''; w = 0; }
      cur += ch; w += cw;
    }
    if (cur !== '') lines.push(cur);
    if (maxLines && lines.length > maxLines) {
      lines = lines.slice(0, maxLines);
      lines[maxLines - 1] = lines[maxLines - 1].slice(0, Math.max(1, lines[maxLines - 1].length - 1)) + '…';
    }
    return lines;
  }

  /* ===================================================================
     1. QRコードエンコーダ（byte モード / モデル2 / バージョン1-40）
        QR-START — 外部ライブラリ非依存の自前実装
     =================================================================== */

  var QRCode = (function () {
    var EXP = new Uint8Array(512), LOG = new Uint8Array(256);
    (function () {
      var x = 1;
      for (var i = 0; i < 255; i++) { EXP[i] = x; LOG[x] = i; x <<= 1; if (x & 0x100) x ^= 0x11D; }
      for (var j = 255; j < 512; j++) EXP[j] = EXP[j - 255];
    })();

    function mul(a, b) { return (a === 0 || b === 0) ? 0 : EXP[LOG[a] + LOG[b]]; }

    // 誤り訂正ブロックあたりのECCコードワード数 [ecl][version]
    var ECC_PER_BLOCK = {
      L: [-1, 7, 10, 15, 20, 26, 18, 20, 24, 30, 18, 20, 24, 26, 30, 22, 24, 28, 30, 28, 28, 28, 28, 30, 30, 26, 28, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30],
      M: [-1, 10, 16, 26, 18, 24, 16, 18, 22, 22, 26, 30, 22, 22, 24, 24, 28, 28, 26, 26, 26, 26, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28],
      Q: [-1, 13, 22, 18, 26, 18, 24, 18, 22, 20, 24, 28, 26, 24, 20, 30, 24, 28, 28, 26, 30, 28, 30, 30, 30, 30, 28, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30],
      H: [-1, 17, 28, 22, 16, 22, 28, 26, 26, 24, 28, 24, 28, 22, 24, 24, 30, 28, 28, 26, 28, 30, 24, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30]
    };
    // 誤り訂正ブロック数 [ecl][version]
    var NUM_BLOCKS = {
      L: [-1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 4, 4, 4, 4, 6, 6, 6, 6, 7, 8, 8, 9, 9, 10, 12, 12, 12, 13, 14, 15, 16, 17, 18, 19, 19, 20, 21, 22, 24, 25],
      M: [-1, 1, 1, 1, 2, 2, 4, 4, 4, 5, 5, 5, 8, 9, 9, 10, 10, 11, 13, 14, 16, 17, 17, 18, 20, 21, 23, 25, 26, 28, 29, 31, 33, 35, 37, 38, 40, 43, 45, 47, 49],
      Q: [-1, 1, 1, 2, 2, 4, 4, 6, 6, 8, 8, 8, 10, 12, 16, 12, 17, 16, 18, 21, 20, 23, 23, 25, 27, 29, 34, 34, 35, 38, 40, 43, 45, 48, 51, 53, 56, 59, 62, 65, 68],
      H: [-1, 1, 1, 2, 4, 4, 4, 5, 6, 8, 8, 11, 11, 16, 16, 18, 16, 19, 21, 25, 25, 25, 34, 30, 32, 35, 37, 40, 42, 45, 48, 51, 54, 57, 60, 63, 66, 70, 74, 77, 81]
    };
    var ECL_FORMAT = { L: 1, M: 0, Q: 3, H: 2 };

    function getBit(x, i) { return ((x >>> i) & 1) !== 0; }

    function rawDataModules(ver) {
      var result = (16 * ver + 128) * ver + 64;
      if (ver >= 2) {
        var numAlign = Math.floor(ver / 7) + 2;
        result -= (25 * numAlign - 10) * numAlign - 55;
        if (ver >= 7) result -= 36;
      }
      return result;
    }

    function dataCodewords(ver, ecl) {
      return Math.floor(rawDataModules(ver) / 8) - ECC_PER_BLOCK[ecl][ver] * NUM_BLOCKS[ecl][ver];
    }

    function alignmentPositions(ver) {
      if (ver === 1) return [];
      var numAlign = Math.floor(ver / 7) + 2;
      var step = (ver === 32) ? 26 : Math.ceil((ver * 4 + 4) / (numAlign * 2 - 2)) * 2;
      var result = [6];
      for (var pos = ver * 4 + 10; result.length < numAlign; pos -= step) result.splice(1, 0, pos);
      return result;
    }

    function toUtf8Bytes(str) {
      var out = [], i, c, c2, cp;
      for (i = 0; i < str.length; i++) {
        c = str.charCodeAt(i);
        if (c < 0x80) out.push(c);
        else if (c < 0x800) { out.push(0xC0 | (c >> 6), 0x80 | (c & 63)); }
        else if (c >= 0xD800 && c <= 0xDBFF && i + 1 < str.length) {
          c2 = str.charCodeAt(i + 1);
          cp = 0x10000 + ((c - 0xD800) << 10) + (c2 - 0xDC00);
          out.push(0xF0 | (cp >> 18), 0x80 | ((cp >> 12) & 63), 0x80 | ((cp >> 6) & 63), 0x80 | (cp & 63));
          i++;
        } else { out.push(0xE0 | (c >> 12), 0x80 | ((c >> 6) & 63), 0x80 | (c & 63)); }
      }
      return out;
    }

    function rsDivisor(degree) {
      var result = new Array(degree).fill(0);
      result[degree - 1] = 1;
      var root = 1;
      for (var i = 0; i < degree; i++) {
        for (var j = 0; j < result.length; j++) {
          result[j] = mul(result[j], root);
          if (j + 1 < result.length) result[j] ^= result[j + 1];
        }
        root = mul(root, 0x02);
      }
      return result;
    }

    function rsRemainder(data, divisor) {
      var result = new Array(divisor.length).fill(0);
      for (var i = 0; i < data.length; i++) {
        var factor = data[i] ^ result.shift();
        result.push(0);
        for (var j = 0; j < result.length; j++) result[j] ^= mul(divisor[j], factor);
      }
      return result;
    }

    function segmentBits(version, bytes) {
      var bits = [];
      function push(val, len) { for (var k = len - 1; k >= 0; k--) bits.push((val >>> k) & 1); }
      push(0x4, 4);                                   // モード: byte
      push(bytes.length, version < 10 ? 8 : 16);      // 文字数
      for (var i = 0; i < bytes.length; i++) push(bytes[i], 8);
      return bits;
    }

    function buildCodewords(version, ecl, bits) {
      var capacity = dataCodewords(version, ecl) * 8;
      var bb = bits.slice(0, capacity);
      bb.push.apply(bb, new Array(Math.min(4, capacity - bb.length)).fill(0)); // ターミネータ
      while (bb.length % 8 !== 0) bb.push(0);
      var data = [];
      for (var i = 0; i < bb.length; i += 8) {
        var b = 0;
        for (var j = 0; j < 8; j++) b = (b << 1) | bb[i + j];
        data.push(b);
      }
      var pad = [0xEC, 0x11], p = 0;
      while (data.length < capacity / 8) { data.push(pad[p % 2]); p++; }

      var numBlocks = NUM_BLOCKS[ecl][version];
      var blockEccLen = ECC_PER_BLOCK[ecl][version];
      var rawCodewords = Math.floor(rawDataModules(version) / 8);
      var numShortBlocks = numBlocks - rawCodewords % numBlocks;
      var shortBlockLen = Math.floor(rawCodewords / numBlocks);
      var divisor = rsDivisor(blockEccLen);
      var blocks = [], k = 0;
      for (var bi = 0; bi < numBlocks; bi++) {
        var datLen = shortBlockLen - blockEccLen + (bi < numShortBlocks ? 0 : 1);
        var dat = data.slice(k, k + datLen); k += datLen;
        var ecc = rsRemainder(dat, divisor);
        var blk = dat.slice();
        if (bi < numShortBlocks) blk.push(0); // インターリーブ時のスキップ用プレースホルダ
        blocks.push(blk.concat(ecc));
      }
      var out = [];
      for (var idx = 0; idx < blocks[0].length; idx++) {
        for (var b2 = 0; b2 < blocks.length; b2++) {
          if (idx !== shortBlockLen - blockEccLen || b2 >= numShortBlocks) out.push(blocks[b2][idx]);
        }
      }
      return out;
    }

    function makeMatrix(version, ecl, codewords, forceMask) {
      var size = version * 4 + 17;
      var modules = [], isFunc = [], y, x;
      for (y = 0; y < size; y++) {
        modules.push(new Array(size).fill(false));
        isFunc.push(new Array(size).fill(false));
      }
      function setFunc(cx, cy, dark) {
        if (cx < 0 || cy < 0 || cx >= size || cy >= size) return;
        modules[cy][cx] = dark; isFunc[cy][cx] = true;
      }
      function finder(cx, cy) {
        for (var dy = -4; dy <= 4; dy++) for (var dx = -4; dx <= 4; dx++) {
          var dist = Math.max(Math.abs(dx), Math.abs(dy));
          setFunc(cx + dx, cy + dy, dist !== 2 && dist !== 4);
        }
      }
      function align(cx, cy) {
        for (var dy = -2; dy <= 2; dy++) for (var dx = -2; dx <= 2; dx++)
          setFunc(cx + dx, cy + dy, Math.max(Math.abs(dx), Math.abs(dy)) !== 1);
      }
      function formatBits(mask) {
        var data = (ECL_FORMAT[ecl] << 3) | mask, rem = data;
        for (var i = 0; i < 10; i++) rem = (rem << 1) ^ ((rem >>> 9) * 0x537);
        var bits = ((data << 10) | rem) ^ 0x5412;
        for (var j = 0; j <= 5; j++) setFunc(8, j, getBit(bits, j));
        setFunc(8, 7, getBit(bits, 6));
        setFunc(8, 8, getBit(bits, 7));
        setFunc(7, 8, getBit(bits, 8));
        for (var m = 9; m < 15; m++) setFunc(14 - m, 8, getBit(bits, m));
        for (var n = 0; n < 8; n++) setFunc(size - 1 - n, 8, getBit(bits, n));
        for (var q = 8; q < 15; q++) setFunc(8, size - 15 + q, getBit(bits, q));
        setFunc(8, size - 8, true);
      }

      // タイミングパターン
      for (var i = 0; i < size; i++) { setFunc(6, i, i % 2 === 0); setFunc(i, 6, i % 2 === 0); }
      // 位置検出パターン
      finder(3, 3); finder(size - 4, 3); finder(3, size - 4);
      // 位置合わせパターン
      var pos = alignmentPositions(version), n2 = pos.length, a, b;
      for (a = 0; a < n2; a++) for (b = 0; b < n2; b++) {
        if ((a === 0 && b === 0) || (a === 0 && b === n2 - 1) || (a === n2 - 1 && b === 0)) continue;
        align(pos[a], pos[b]);
      }
      // バージョン情報（v7以降）
      if (version >= 7) {
        var vrem = version;
        for (var vi = 0; vi < 12; vi++) vrem = (vrem << 1) ^ ((vrem >>> 11) * 0x1F25);
        var vbits = (version << 12) | vrem;
        for (var p = 0; p < 18; p++) {
          var bit = getBit(vbits, p);
          var ax = size - 11 + p % 3, ay = Math.floor(p / 3);
          setFunc(ax, ay, bit); setFunc(ay, ax, bit);
        }
      }
      formatBits(0); // 予約（後でマスクごとに描き直す）

      // データ配置（右下から左右ジグザグ）
      var di = 0, total = codewords.length * 8;
      for (var right = size - 1; right >= 1; right -= 2) {
        if (right === 6) right = 5;
        for (var vert = 0; vert < size; vert++) {
          for (var jj = 0; jj < 2; jj++) {
            var xx = right - jj;
            var upward = ((right + 1) & 2) === 0;
            var yy = upward ? size - 1 - vert : vert;
            if (!isFunc[yy][xx] && di < total) {
              modules[yy][xx] = getBit(codewords[di >>> 3], 7 - (di & 7));
              di++;
            }
          }
        }
      }

      function applyMask(mask) {
        for (var yy = 0; yy < size; yy++) for (var xx = 0; xx < size; xx++) {
          if (isFunc[yy][xx]) continue;
          var invert;
          switch (mask) {
            case 0: invert = (xx + yy) % 2 === 0; break;
            case 1: invert = yy % 2 === 0; break;
            case 2: invert = xx % 3 === 0; break;
            case 3: invert = (xx + yy) % 3 === 0; break;
            case 4: invert = (Math.floor(xx / 3) + Math.floor(yy / 2)) % 2 === 0; break;
            case 5: invert = (xx * yy) % 2 + (xx * yy) % 3 === 0; break;
            case 6: invert = ((xx * yy) % 2 + (xx * yy) % 3) % 2 === 0; break;
            default: invert = ((xx + yy) % 2 + (xx * yy) % 3) % 2 === 0; break;
          }
          if (invert) modules[yy][xx] = !modules[yy][xx];
        }
      }

      function penalty() {
        var result = 0, P1 = 3, P2 = 3, P3 = 40, P4 = 10, runHistory;
        function addHistory(len) {
          if (runHistory[0] === 0) len += size;
          runHistory.pop(); runHistory.unshift(len);
        }
        function countPatterns() {
          var n = runHistory[1];
          var core = n > 0 && runHistory[2] === n && runHistory[3] === n * 3 && runHistory[4] === n && runHistory[5] === n;
          return (core && runHistory[0] >= n * 4 && runHistory[6] >= n ? 1 : 0) +
                 (core && runHistory[6] >= n * 4 && runHistory[0] >= n ? 1 : 0);
        }
        function terminate(color, len) {
          if (color) { addHistory(len); len = 0; }
          len += size; addHistory(len);
          return countPatterns();
        }
        var i, j, color, run;
        for (i = 0; i < size; i++) {
          color = false; run = 0; runHistory = new Array(7).fill(0);
          for (j = 0; j < size; j++) {
            if (modules[i][j] === color) { run++; if (run === 5) result += P1; else if (run > 5) result++; }
            else { addHistory(run); if (!color) result += countPatterns() * P3; color = modules[i][j]; run = 1; }
          }
          result += terminate(color, run) * P3;
        }
        for (j = 0; j < size; j++) {
          color = false; run = 0; runHistory = new Array(7).fill(0);
          for (i = 0; i < size; i++) {
            if (modules[i][j] === color) { run++; if (run === 5) result += P1; else if (run > 5) result++; }
            else { addHistory(run); if (!color) result += countPatterns() * P3; color = modules[i][j]; run = 1; }
          }
          result += terminate(color, run) * P3;
        }
        for (i = 0; i < size - 1; i++) for (j = 0; j < size - 1; j++) {
          var c = modules[i][j];
          if (c === modules[i][j + 1] && c === modules[i + 1][j] && c === modules[i + 1][j + 1]) result += P2;
        }
        var dark = 0;
        for (i = 0; i < size; i++) for (j = 0; j < size; j++) if (modules[i][j]) dark++;
        var total = size * size;
        result += (Math.ceil(Math.abs(dark * 20 - total * 10) / total) - 1) * P4;
        return result;
      }

      var bestMask = 0, bestPenalty = Infinity;
      if (forceMask != null) {
        bestMask = forceMask;
      } else {
        for (var mask = 0; mask < 8; mask++) {
          applyMask(mask); formatBits(mask);
          var pen = penalty();
          if (pen < bestPenalty) { bestPenalty = pen; bestMask = mask; }
          applyMask(mask); // 元に戻す
        }
      }
      applyMask(bestMask); formatBits(bestMask);
      return { size: size, modules: modules, mask: bestMask, version: version };
    }

    /* text を QR 化。ecl は 'L'|'M'|'Q'|'H'。forceMask は検証用（通常は未指定） */
    function encode(text, ecl, forceMask) {
      ecl = ECL_FORMAT[ecl] !== undefined ? ecl : 'M';
      var bytes = toUtf8Bytes(String(text));
      var version = 0;
      for (var v = 1; v <= 40; v++) {
        var ccBits = v < 10 ? 8 : 16;
        if (4 + ccBits + bytes.length * 8 <= dataCodewords(v, ecl) * 8) { version = v; break; }
      }
      if (!version) throw new Error('QR: データが長すぎます');
      var bits = segmentBits(version, bytes);
      var codewords = buildCodewords(version, ecl, bits);
      return makeMatrix(version, ecl, codewords, forceMask);
    }

    return { encode: encode };
  })();
  /* QR-END */

  /* ===================================================================
     2. 定数（配色・フォント）
     =================================================================== */

  var PALETTE_MAIN = {
    mono: '#1f1f1f',
    navy: '#14386b',
    green: '#14532d',
    wine: '#7a1f2b'
  };

  var FONT_STACK = {
    mincho: "'Noto Serif JP','Hiragino Mincho ProN','Yu Mincho','YuMincho',serif",
    gothic: "'Noto Sans JP','Hiragino Kaku Gothic ProN','Yu Gothic','Meiryo',sans-serif"
  };

  var PH_COLOR = '#c9cfdb';
  var LIGHT_RULE = 0.62;

  /* ===================================================================
     3. 状態
     =================================================================== */

  var state = {
    lang: 'ja',
    template: 'center',
    orientation: 'landscape',
    palette: 'mono',
    customColor: '#2b5cab',
    font: 'gothic',
    qr: false,
    transparent: false
  };

  function mainColor() {
    return state.palette === 'custom' ? state.customColor : (PALETTE_MAIN[state.palette] || '#1f1f1f');
  }

  function readFields() {
    function v(id) { var el = byId(id); return el ? trim(el.value) : ''; }
    return {
      name: v('name'), kana: v('kana'), company: v('company'),
      dept: v('dept'), title: v('title'), zip: v('zip'), address: v('address'),
      tel: v('tel'), fax: v('fax'), email: v('email'), url: v('url')
    };
  }

  /* ===================================================================
     4. SVG 生成
     =================================================================== */

  function cardSize() {
    return state.orientation === 'portrait' ? { w: 55, h: 91 } : { w: 91, h: 55 };
  }

  /* 値と表示色を返す（空欄時はプレースホルダ or 非表示） */
  function pick(value, ph, opts, mainCol) {
    var t = trim(value);
    if (t) return { t: t, fill: mainCol };
    if (opts.placeholders) return { t: ph, fill: PH_COLOR };
    return { t: '', fill: mainCol };
  }

  function txt(s, x, y, size, fill, opts) {
    if (!s) return '';
    opts = opts || {};
    var a = '<text x="' + x + '" y="' + y + '" font-size="' + size + '" fill="' + fill + '"';
    if (opts.w) a += ' font-weight="' + opts.w + '"';
    if (opts.anchor) a += ' text-anchor="' + opts.anchor + '"';
    if (opts.spacing) a += ' letter-spacing="' + opts.spacing + '"';
    return a + '>' + esc(s) + '</text>';
  }

  function vcol(s, x, y0, size, step, fill, w, maxChars) {
    if (!s) return '';
    var t = s;
    if (maxChars && t.length > maxChars) t = t.slice(0, maxChars - 1) + '…';
    var out = '';
    for (var i = 0; i < t.length; i++) {
      if (t[i] === ' ') continue;
      out += txt(t[i], x, (y0 + i * step).toFixed(2), size, fill, { w: w, anchor: 'middle' });
    }
    return out;
  }

  function joinParts(parts) {
    return parts.filter(function (p) { return p && trim(p); }).join('　');
  }

  function telLine(f) {
    var a = [];
    if (f.tel) a.push('TEL ' + f.tel);
    if (f.fax) a.push('FAX ' + f.fax);
    return a.join('　');
  }

  function webLine(f) {
    var a = [];
    if (f.email) a.push(f.email);
    if (f.url) a.push(f.url);
    return a.join('　');
  }

  function addrLine(f) {
    if (f.zip && f.address) return '〒' + f.zip + ' ' + f.address;
    if (f.zip) return '〒' + f.zip;
    return f.address;
  }

  /* 連絡先を最大 maxLines 行に整形（折り返しあり） */
  function contactLines(f, availMM, sizeMM, maxLines) {
    var maxEm = availMM / sizeMM;
    var logical = [addrLine(f), telLine(f), webLine(f)];
    var out = [];
    for (var i = 0; i < logical.length; i++) {
      if (!trim(logical[i])) continue;
      var ls = wrapText(logical[i], maxEm, 2);
      for (var j = 0; j < ls.length; j++) out.push(ls[j]);
    }
    if (out.length > maxLines) out = out.slice(0, maxLines);
    return out;
  }

  /* QRコード（SVGグループ）。URLが空なら点線プレースホルダ */
  function qrGroup(url, x, y, sizeMM, opts) {
    opts = opts || {};
    if (!trim(url)) {
      return '<g>' +
        '<rect x="' + x + '" y="' + y + '" width="' + sizeMM + '" height="' + sizeMM + '" fill="#ffffff" stroke="#b9c0cd" stroke-width="0.25" stroke-dasharray="1 0.8"/>' +
        txt(opts.label || 'QR', x + sizeMM / 2, y + sizeMM / 2 + 0.9, 2, '#b9c0cd', { anchor: 'middle' }) +
        '</g>';
    }
    var qr;
    try { qr = QRCode.encode(url, 'M'); } catch (e) { return ''; }
    var n = qr.size, total = n + 8, m = sizeMM / total;
    var out = ['<g shape-rendering="crispEdges">'];
    out.push('<rect x="' + x.toFixed(3) + '" y="' + y.toFixed(3) + '" width="' + sizeMM + '" height="' + sizeMM + '" fill="#ffffff"/>');
    for (var r = 0; r < n; r++) {
      for (var c = 0; c < n; c++) {
        if (!qr.modules[r][c]) continue;
        out.push('<rect x="' + (x + (c + 4) * m).toFixed(3) + '" y="' + (y + (r + 4) * m).toFixed(3) +
          '" width="' + m.toFixed(3) + '" height="' + m.toFixed(3) + '" fill="#000000"/>');
      }
    }
    out.push('</g>');
    return out.join('');
  }

  /* ---------- レイアウト：中央揃え ---------- */
  function layoutCenter(f, c, opts) {
    var s = cardSize(), W = s.w, H = s.h, out = [];
    var landscape = state.orientation === 'landscape';
    var qrSize = 15, qrPad = 4;
    var body = [], cx, y, i;

    if (landscape) {
      cx = state.qr ? 34 : 45.5;
      y = 11;
      var comp = pick(f.company, '会社名', opts, c.main);
      body.push(txt(comp.t, 45.5, y, 3.4, comp.fill, { w: 600, anchor: 'middle', spacing: 0.08 }));
      var dt = pick(joinParts([f.dept, f.title]), '部署・役職', opts, c.main);
      body.push(txt(dt.t, 45.5, y + 4.8, 2.7, dt.fill, { anchor: 'middle' }));
      var nm = pick(f.name, '氏名', opts, c.main);
      body.push(txt(nm.t, 45.5, 27, 7.4, nm.fill, { w: 700, anchor: 'middle', spacing: 0.06 }));
      var kn = pick(f.kana, 'フリガナ', opts, c.main);
      body.push(txt(kn.t, 45.5, 31.6, 2.3, kn.fill, { anchor: 'middle', spacing: 0.12 }));
      body.push('<line x1="' + (cx === 34 ? 22 : 34) + '" y1="34.3" x2="' + (cx === 34 ? 46 : 57) + '" y2="34.3" stroke="' + c.accent + '" stroke-width="0.6" stroke-linecap="round"/>');
      var avail = state.qr ? 60 : 78;
      var lines = contactLines(f, avail, 2.3, 4);
      for (i = 0; i < lines.length; i++) body.push(txt(lines[i], cx, 38.6 + i * 3.6, 2.3, c.sub, { anchor: 'middle' }));
      if (state.qr) body.push(qrGroup(f.url, W - qrPad - qrSize, H - qrPad - qrSize, qrSize, { label: opts.qrLabel }));
    } else {
      cx = state.qr ? 20.5 : 27.5;
      body.push(txt(pick(f.company, '会社名', opts, c.main).t, 27.5, 22, 3.5, pick(f.company, '会社名', opts, c.main).fill, { w: 600, anchor: 'middle' }));
      var dt2 = pick(joinParts([f.dept, f.title]), '部署・役職', opts, c.main);
      body.push(txt(dt2.t, 27.5, 26.8, 2.7, dt2.fill, { anchor: 'middle' }));
      var nm2 = pick(f.name, '氏名', opts, c.main);
      body.push(txt(nm2.t, 27.5, 44, 7.8, nm2.fill, { w: 700, anchor: 'middle', spacing: 0.06 }));
      var kn2 = pick(f.kana, 'フリガナ', opts, c.main);
      body.push(txt(kn2.t, 27.5, 49, 2.3, kn2.fill, { anchor: 'middle', spacing: 0.12 }));
      body.push('<line x1="16.5" y1="53" x2="38.5" y2="53" stroke="' + c.accent + '" stroke-width="0.6" stroke-linecap="round"/>');
      var avail2 = state.qr ? 30 : 45;
      var lines2 = contactLines(f, avail2, 2.3, 5);
      for (i = 0; i < lines2.length; i++) body.push(txt(lines2[i], cx, 59.5 + i * 4, 2.3, c.sub, { anchor: 'middle' }));
      if (state.qr) body.push(qrGroup(f.url, W - qrPad - 14, H - qrPad - 14, 14, { label: opts.qrLabel }));
    }
    out.push(body.join(''));
    return out.join('');
  }

  /* ---------- レイアウト：左揃え ---------- */
  function layoutLeft(f, c, opts) {
    var s = cardSize(), W = s.w, H = s.h, out = [];
    var landscape = state.orientation === 'landscape';
    var body = [], i;

    if (landscape) {
      body.push('<rect x="5.6" y="22" width="1.05" height="11" fill="' + c.accent + '"/>');
      var comp = pick(f.company, '会社名', opts, c.main);
      body.push(txt(comp.t, 8.6, 12, 3.6, comp.fill, { w: 700 }));
      var dt = pick(joinParts([f.dept, f.title]), '部署・役職', opts, c.main);
      body.push(txt(dt.t, 8.6, 17, 2.7, dt.fill, {}));
      var nm = pick(f.name, '氏名', opts, c.main);
      body.push(txt(nm.t, 8.6, 30.5, 7, nm.fill, { w: 700, spacing: 0.06 }));
      var kn = pick(f.kana, 'フリガナ', opts, c.main);
      body.push(txt(kn.t, 8.6, 35.2, 2.3, kn.fill, { spacing: 0.12 }));
      body.push('<line x1="6" y1="38.7" x2="85" y2="38.7" stroke="' + c.rule + '" stroke-width="0.25"/>');

      if (state.qr) {
        var linesS = contactLines(f, 58, 2.1, 4);
        for (i = 0; i < linesS.length; i++) body.push(txt(linesS[i], 6, 42.6 + i * 3.3, 2.1, c.sub, {}));
        body.push(qrGroup(f.url, W - 4 - 15, H - 4 - 15, 15, { label: opts.qrLabel }));
      } else {
        var addr = wrapText(addrLine(f), 40 / 2.2, 3);
        if (!addr.length && opts.placeholders) addr = ['〒000-0000 住所'];
        for (i = 0; i < addr.length; i++) body.push(txt(addr[i], 6, 42.8 + i * 3.4, 2.2, c.sub, {}));
        var right = contactLines({ tel: f.tel, fax: f.fax, email: f.email, url: f.url, address: '' }, 40, 2.2, 3);
        if (!right.length && opts.placeholders) right = ['TEL・FAX・メール'];
        for (i = 0; i < right.length; i++) body.push(txt(right[i], 48, 42.8 + i * 3.4, 2.2, c.sub, {}));
      }
    } else {
      body.push('<rect x="5.6" y="27" width="1.05" height="11" fill="' + c.accent + '"/>');
      var comp2 = pick(f.company, '会社名', opts, c.main);
      body.push(txt(comp2.t, 8.6, 17, 3.7, comp2.fill, { w: 700 }));
      var dt2 = pick(joinParts([f.dept, f.title]), '部署・役職', opts, c.main);
      body.push(txt(dt2.t, 8.6, 22, 2.8, dt2.fill, {}));
      var nm2 = pick(f.name, '氏名', opts, c.main);
      body.push(txt(nm2.t, 8.6, 37, 7.6, nm2.fill, { w: 700, spacing: 0.06 }));
      var kn2 = pick(f.kana, 'フリガナ', opts, c.main);
      body.push(txt(kn2.t, 8.6, 42.2, 2.3, kn2.fill, { spacing: 0.12 }));
      body.push('<line x1="6" y1="47" x2="48" y2="47" stroke="' + c.rule + '" stroke-width="0.25"/>');
      var avail = state.qr ? 26 : 40;
      var lines = contactLines(f, avail, 2.35, state.qr ? 7 : 6);
      for (i = 0; i < lines.length; i++) body.push(txt(lines[i], 8, 53 + i * (state.qr ? 4 : 4.3), 2.35, c.sub, {}));
      if (state.qr) body.push(qrGroup(f.url, W - 4 - 13, H - 4 - 13, 13, { label: opts.qrLabel }));
    }
    out.push(body.join(''));
    return out.join('');
  }

  /* ---------- レイアウト：縦書き（縦向き固定） ---------- */
  function layoutVertical(f, c, opts) {
    var W = 55, H = 91, body = [];
    var qrSize = 13, qrX = 38, qrY = 74;
    body.push('<rect x="51.4" y="12" width="0.9" height="18" fill="' + c.accent + '"/>');

    var kn = pick(f.kana, 'フリガナ', opts, c.main);
    body.push(vcol(kn.t, 47.5, 12, 2.15, 3.4, kn.fill, 400, 14));

    var nm = pick(f.name, '氏名', opts, c.main);
    body.push(vcol(nm.t, 40, 13, 7.2, 8.4, nm.fill, 700, 6));

    var comp = pick(f.company, '会社名', opts, c.main);
    body.push(vcol(comp.t, 30.5, 12, 3.4, 4.2, comp.fill, 700, 11));

    var dt = pick(joinParts([f.dept, f.title]), '部署・役職', opts, c.main);
    body.push(vcol(dt.t, 23, 12, 2.5, 3.6, dt.fill, 400, 12));

    // 連絡先は下部に横組みで（長いメール・URLも欠けずに収める）
    var lines = contactLines(f, 46, 2, 5);
    for (var i = 0; i < lines.length; i++) {
      body.push(txt(lines[i], 5.5, 58 + i * 3.5, 2, c.sub, {}));
    }

    body.push(qrGroup(f.url, qrX, qrY, qrSize, { label: opts.qrLabel }));
    return body.join('');
  }

  var LAYOUTS = { center: layoutCenter, left: layoutLeft, vertical: layoutVertical };

  /* 名刺1枚のSVG文字列を生成 */
  function buildCardSVG(f, opts) {
    opts = opts || {};
    var s = cardSize(), W = s.w, H = s.h;
    var main = mainColor();
    var c = {
      main: main,
      accent: main,
      sub: lighten(main, 0.18),
      rule: lighten(main, LIGHT_RULE)
    };
    var font = FONT_STACK[state.font] || FONT_STACK.gothic;
    var layout = LAYOUTS[state.template] || layoutCenter;

    var px = opts.px || 0;
    var wAttr = px ? px + 'px' : W + 'mm';
    var hAttr = px ? Math.round(px * H / W) + 'px' : H + 'mm';

    var parts = [];
    parts.push('<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 ' + W + ' ' + H + '" width="' + wAttr + '" height="' + hAttr + '" role="img" aria-label="名刺プレビュー">');
    if (!opts.transparent) parts.push('<rect x="0" y="0" width="' + W + '" height="' + H + '" fill="#ffffff"/>');
    parts.push('<g font-family="' + font + '">');
    parts.push(layout(f, c, opts));
    parts.push('</g></svg>');
    return parts.join('');
  }

  /* ===================================================================
     5. 描画
     =================================================================== */

  var previewEl, stageEl;

  function render() {
    var f = readFields();
    var opts = { placeholders: true, qrLabel: 'QR' };
    var svg = buildCardSVG(f, opts);
    previewEl.innerHTML = svg;
    previewEl.classList.toggle('is-portrait', state.orientation === 'portrait');
    previewEl.classList.toggle('is-transparent', state.transparent);
    updateNote();

    // 縦書きは縦向き固定
    var portraitRadio = byId('oriPortrait'), landscapeRadio = byId('oriLandscape');
    if (portraitRadio && landscapeRadio) {
      var lock = state.template === 'vertical';
      portraitRadio.disabled = lock;
      landscapeRadio.disabled = lock;
    }
  }

  function updateNote() {
    var note = byId('previewNote');
    if (!note) return;
    note.textContent = state.orientation === 'portrait'
      ? tr('previewNoteP')
      : tr('previewNoteL');
  }

  /* ===================================================================
     6. 印刷（A4・実寸mm）
     =================================================================== */

  function buildSheet() {
    var sheet = byId('printSheet');
    if (!sheet) return;
    var f = readFields();
    var opts = { placeholders: false, qrLabel: 'QR' };
    var svg = buildCardSVG(f, opts);
    var portrait = state.orientation === 'portrait';
    var count = portrait ? 9 : 10;
    var cells = [];
    for (var i = 0; i < count; i++) cells.push('<div class="sheet-cell">' + svg + '</div>');
    sheet.innerHTML = '<div class="sheet-grid' + (portrait ? ' is-portrait' : '') + '">' + cells.join('') + '</div>';
  }

  function doPrint() {
    buildSheet();
    window.print();
  }

  /* ===================================================================
     7. PNG保存（SVG → Canvas → toBlob。file:// でも外部参照なしで安全）
     =================================================================== */

  function exportPng() {
    var f = readFields();
    var px = 800;
    var svg = buildCardSVG(f, { placeholders: false, transparent: state.transparent, px: px, qrLabel: 'QR' });
    var url = 'data:image/svg+xml;charset=utf-8,' + encodeURIComponent(svg);
    var img = new Image();
    img.onload = function () {
      var s = cardSize();
      var w = px, h = Math.round(px * s.h / s.w);
      var cv = document.createElement('canvas');
      cv.width = w; cv.height = h;
      var ctx = cv.getContext('2d');
      ctx.clearRect(0, 0, w, h);
      ctx.drawImage(img, 0, 0, w, h);
      try {
        cv.toBlob(function (blob) {
          if (!blob) { notify(tr('pngFail')); return; }
          var a = document.createElement('a');
          a.href = URL.createObjectURL(blob);
          a.download = fileName(f);
          document.body.appendChild(a);
          a.click();
          document.body.removeChild(a);
          setTimeout(function () { URL.revokeObjectURL(a.href); }, 4000);
        }, 'image/png');
      } catch (e) {
        notify(tr('pngFail'));
      }
    };
    img.onerror = function () { notify(tr('pngFail')); };
    img.src = url;
  }

  function fileName(f) {
    var base = trim(f.name) || trim(f.company) || 'meishi';
    base = base.replace(/[\\/:*?"<>|\s]+/g, '_').slice(0, 24);
    return 'meishi-' + base + '.png';
  }

  var notifyTimer = null;
  function notify(msg) {
    var el = byId('toast');
    if (!el) {
      el = document.createElement('div');
      el.id = 'toast';
      el.className = 'toast';
      document.body.appendChild(el);
    }
    el.textContent = msg;
    el.classList.add('is-on');
    if (notifyTimer) clearTimeout(notifyTimer);
    notifyTimer = setTimeout(function () { el.classList.remove('is-on'); }, 2200);
  }

  /* ===================================================================
     8. シェア
     =================================================================== */

  var SHARE_URL = 'https://www.reveriel.com/meishi-generator/';

  function shareText() { return tr('shareText'); }

  function openUrl(u) { window.open(u, '_blank', 'noopener,noreferrer'); }

  function copyText(text) {
    return new Promise(function (resolve) {
      if (navigator.clipboard && window.isSecureContext) {
        navigator.clipboard.writeText(text).then(function () { resolve(true); }, function () { resolve(fallbackCopy(text)); });
      } else {
        resolve(fallbackCopy(text));
      }
    });
  }

  function fallbackCopy(text) {
    try {
      var ta = document.createElement('textarea');
      ta.value = text;
      ta.setAttribute('readonly', '');
      ta.style.position = 'fixed';
      ta.style.top = '-1000px';
      document.body.appendChild(ta);
      ta.select();
      var ok = document.execCommand('copy');
      document.body.removeChild(ta);
      return ok;
    } catch (e) { return false; }
  }

  /* ===================================================================
     9. 多言語（中文 ⇄ 日本語）— 画面のみ。名刺は入力どおり表示。
     =================================================================== */

  var I18N = {
    brandName: { ja: '名刺作成ツール', zh: '名片製作工具' },
    tagline: { ja: '無料・登録不要・ブラウザだけで完結', zh: '免费・无需注册・浏览器内完成' },
    btnPrint: { ja: 'A4に10枚印刷', zh: 'A4一页印10张' },
    btnPrintShort: { ja: '印刷する', zh: '打印' },
    btnPng: { ja: 'PNG保存', zh: '保存 PNG' },
    btnSample: { ja: '記入例を入れる', zh: '填入示例' },
    btnReset: { ja: 'リセット', zh: '清空重填' },
    btnLang: { ja: '中文', zh: '日本語' },

    formTitle: { ja: '情報を入力して名刺をつくる', zh: '填写信息，生成名片' },
    formHint: { ja: '左に入力すると、右の名刺プレビューが実寸（91×55mm）でリアルタイムに更新されます。最後に「A4に10枚印刷」または「PNG保存」を選んでください。', zh: '在左侧输入，右侧会以实际尺寸（91×55mm）实时更新名片预览。最后选择「A4一页印10张」或「保存 PNG」。' },
    noticeTitle: { ja: 'はじめての方へ', zh: '初次使用' },
    noticeBody: { ja: '入力内容はサーバーに送信されません。すべてお使いのブラウザ内で処理されます。まずは「記入例を入れる」で完成イメージを確認するのがおすすめです。', zh: '输入内容不会发送到服务器，全部在你的浏览器内处理。建议先点「填入示例」看看成品效果。' },

    legendPerson: { ja: '基本情報', zh: '基本信息' },
    badgeRequired: { ja: '氏名は必須', zh: '姓名必填' },
    lblName: { ja: '氏名', zh: '姓名' },
    phName: { ja: '例：山田 太郎', zh: '例：山田 太郎' },
    lblKana: { ja: 'フリガナ', zh: '假名（フリガナ）' },
    phKana: { ja: '例：ヤマダ タロウ', zh: '例：ヤマダ タロウ' },
    helpKana: { ja: 'カタカナで入力すると、名刺にフリガナとして小さく表示されます。', zh: '用片假名输入后，会在名片上以假名小字显示。' },
    lblCompany: { ja: '会社名・屋号', zh: '公司名・商号' },
    phCompany: { ja: '例：山田デザイン事務所', zh: '例：山田デザイン事務所' },
    lblDept: { ja: '部署', zh: '部门' },
    phDept: { ja: '例：営業部', zh: '例：営業部' },
    lblTitle: { ja: '役職', zh: '职位' },
    phTitle: { ja: '例：代表取締役', zh: '例：代表取締役' },

    legendContact: { ja: '連絡先', zh: '联系方式' },
    lblZip: { ja: '郵便番号', zh: '邮编' },
    phZip: { ja: '例：150-0001', zh: '例：150-0001' },
    lblAddress: { ja: '住所', zh: '地址' },
    phAddress: { ja: '例：東京都渋谷区神宮前1-2-3 ○○ビル5F', zh: '例：東京都渋谷区神宮前1-2-3 ○○ビル5F' },
    lblTel: { ja: '電話番号', zh: '电话' },
    phTel: { ja: '例：03-1234-5678', zh: '例：03-1234-5678' },
    lblFax: { ja: 'FAX', zh: '传真' },
    phFax: { ja: '例：03-1234-5679', zh: '例：03-1234-5679' },
    lblEmail: { ja: 'メールアドレス', zh: '邮箱' },
    phEmail: { ja: '例：taro@yamada-design.jp', zh: '例：taro@yamada-design.jp' },
    lblUrl: { ja: 'URL（Webサイト・SNS）', zh: 'URL（网站・SNS）' },
    phUrl: { ja: '例：https://yamada-design.jp', zh: '例：https://yamada-design.jp' },

    legendDesign: { ja: 'デザイン', zh: '设计' },
    lblTemplate: { ja: 'レイアウトテンプレート', zh: '版式模板' },
    tplCenter: { ja: '中央揃え', zh: '居中' },
    tplCenterDesc: { ja: '氏名を中央に大きく', zh: '姓名居中放大' },
    tplLeft: { ja: '左揃え', zh: '左对齐' },
    tplLeftDesc: { ja: 'すっきり縦のライン', zh: '利落的竖向线条' },
    tplVertical: { ja: '縦書き', zh: '竖排' },
    tplVerticalDesc: { ja: '和風・縦向き55×91', zh: '和风・竖向55×91' },
    lblOrientation: { ja: '名刺の向き', zh: '名片方向' },
    oriLandscape: { ja: '横向き 91×55mm', zh: '横向 91×55mm' },
    oriPortrait: { ja: '縦向き 55×91mm', zh: '竖向 55×91mm' },
    helpOrientation: { ja: '縦書きテンプレートを選ぶと縦向きに固定されます。印刷は横向きならA4に10枚、縦向きなら9枚です。', zh: '选择竖排模板时会固定为竖向。打印时横向为A4一页10张，竖向为9张。' },
    lblColor: { ja: '配色', zh: '配色' },
    palMono: { ja: 'モノクロ', zh: '黑白' },
    palNavy: { ja: '紺', zh: '藏青' },
    palGreen: { ja: '深緑', zh: '深绿' },
    palWine: { ja: 'ワイン', zh: '酒红' },
    palCustom: { ja: 'カスタム', zh: '自定义' },
    lblCustomColor: { ja: 'メインカラー', zh: '主色' },
    lblFont: { ja: 'フォント', zh: '字体' },
    fontMincho: { ja: '明朝体', zh: '明朝体' },
    fontGothic: { ja: 'ゴシック体', zh: '黑体（ゴシック）' },

    legendOptions: { ja: 'オプション', zh: '选项' },
    chkQr: { ja: 'QRコードを入れる（URL欄のアドレスを読み取れます）', zh: '加入二维码（可读取 URL 栏的地址）' },
    helpQr: { ja: 'URL欄が空のときは、QRコードの代わりに点線のプレースホルダーが表示されます。QRコードはブラウザ内で生成され、外部サービスには送信されません。', zh: 'URL 栏为空时，会显示虚线占位框代替二维码。二维码在浏览器内生成，不会发送到外部服务。' },
    chkTransparent: { ja: 'PNG保存時に背景を透明にする（印刷には影響しません）', zh: '保存 PNG 时背景透明（不影响打印）' },

    previewTitle: { ja: 'プレビュー', zh: '预览' },
    previewNoteL: { ja: '実寸（91×55mm）で表示しています。※端末によっては縮小表示されます。', zh: '按实际尺寸（91×55mm）显示。※部分设备会自动缩小显示。' },
    previewNoteP: { ja: '実寸（55×91mm）で表示しています。※端末によっては縮小表示されます。', zh: '按实际尺寸（55×91mm）显示。※部分设备会自动缩小显示。' },
    tipTitle: { ja: '印刷のコツ', zh: '打印小贴士' },
    tip1: { ja: '用紙は「厚口マット紙」か「名刺用紙」がおすすめです。', zh: '纸张推荐「厚口哑光纸」或专用名片纸。' },
    tip2: { ja: 'プリンターの設定で「拡大/縮小」を「100%（実際のサイズ）」にしてください。', zh: '打印设置里把「缩放」设为「100%（实际大小）」。' },
    tip3: { ja: '印刷後は各名刺の薄い罫線に沿ってカッターで切り分けます。', zh: '打印后沿每张名片的浅色裁切线用裁纸刀裁开。' },

    shareTitle: { ja: 'このツールをシェアする', zh: '分享这个工具' },
    shareX: { ja: 'X で共有', zh: '分享到 X' },
    shareLine: { ja: 'LINE で共有', zh: '分享到 LINE' },
    shareCopy: { ja: 'リンクをコピー', zh: '复制链接' },
    shareText: { ja: '無料で名刺が作れるツールを見つけました。テンプレートを選んで入力するだけで、A4に10枚印刷できる名刺が作れます。', zh: '发现一个免费做名片的工具，选模板填信息就能生成，还能 A4 一页印 10 张。' },
    copied: { ja: 'コピーしました', zh: '已复制' },
    copyFail: { ja: 'コピーできませんでした', zh: '复制失败' },
    pngFail: { ja: 'PNGの保存に失敗しました', zh: 'PNG 保存失败' },

    footerText: { ja: '名刺作成ツール — 無料テンプレートで名刺をデザイン・A4に10枚印刷できるブラウザ完結型ツール', zh: '名片製作工具 — 免费模板设计名片，A4 一页印 10 张的纯浏览器工具' }
  };

  function tr(key) {
    var e = I18N[key];
    if (!e) return key;
    return e[state.lang] || e.ja || key;
  }

  function applyI18n(lang) {
    state.lang = lang === 'zh' ? 'zh' : 'ja';
    document.documentElement.lang = state.lang === 'zh' ? 'zh-CN' : 'ja';

    qsa('[data-i18n]').forEach(function (el) {
      var key = el.getAttribute('data-i18n');
      var e = I18N[key];
      if (e) el.textContent = e[state.lang] || e.ja;
    });
    qsa('[data-i18n-ph]').forEach(function (el) {
      var key = el.getAttribute('data-i18n-ph');
      var e = I18N[key];
      if (e) el.setAttribute('placeholder', e[state.lang] || e.ja);
    });
    var langBtn = byId('langBtn');
    if (langBtn) langBtn.textContent = tr('btnLang');
    updateNote();
  }

  /* ===================================================================
     10. フォーム操作
     =================================================================== */

  var SAMPLE = {
    name: '山田 太郎', kana: 'ヤマダ タロウ',
    company: '山田デザイン事務所', dept: 'デザイン部', title: '代表',
    zip: '150-0001', address: '東京都渋谷区神宮前1-2-3 ○○ビル5F',
    tel: '03-1234-5678', fax: '03-1234-5679',
    email: 'taro@yamada-design.jp', url: 'https://yamada-design.jp'
  };

  function fillSample() {
    Object.keys(SAMPLE).forEach(function (k) {
      var el = byId(k);
      if (el) el.value = SAMPLE[k];
    });
    render();
  }

  function resetForm() {
    var form = byId('cardForm');
    if (form) form.reset();
    state.template = 'center';
    state.orientation = 'landscape';
    state.palette = 'mono';
    state.font = 'gothic';
    state.qr = false;
    state.transparent = false;
    var cc = byId('customColor');
    if (cc) cc.value = '#2b5cab';
    syncControls();
    render();
  }

  /* 状態 → コントロールへ反映 */
  function syncControls() {
    var t = document.querySelector('input[name="template"][value="' + state.template + '"]');
    if (t) t.checked = true;
    var o = document.querySelector('input[name="orientation"][value="' + state.orientation + '"]');
    if (o) o.checked = true;
    var f = document.querySelector('input[name="font"][value="' + state.font + '"]');
    if (f) f.checked = true;
    var q = byId('qrCheck'); if (q) q.checked = state.qr;
    var tr2 = byId('bgTransparent'); if (tr2) tr2.checked = state.transparent;
    qsa('.swatch').forEach(function (b) {
      b.classList.toggle('is-active', b.getAttribute('data-palette') === state.palette);
    });
    var row = byId('customColorRow');
    if (row) row.hidden = state.palette !== 'custom';
    var dot = byId('customSwatchDot');
    if (dot) dot.style.background = state.customColor;
  }

  /* ===================================================================
     11. 初期化
     =================================================================== */

  function init() {
    previewEl = byId('cardPreview');
    stageEl = byId('cardStage');

    var form = byId('cardForm');
    if (form) {
      form.addEventListener('input', render);
      form.addEventListener('change', render);
    }

    // テンプレート
    qsa('input[name="template"]').forEach(function (r) {
      r.addEventListener('change', function () {
        if (!r.checked) return;
        state.template = r.value;
        if (state.template === 'vertical') state.orientation = 'portrait';
        syncControls();
        render();
      });
    });

    // 向き
    qsa('input[name="orientation"]').forEach(function (r) {
      r.addEventListener('change', function () {
        if (!r.checked) return;
        state.orientation = r.value;
        render();
      });
    });

    // フォント
    qsa('input[name="font"]').forEach(function (r) {
      r.addEventListener('change', function () {
        if (r.checked) { state.font = r.value; render(); }
      });
    });

    // 配色
    qsa('.swatch').forEach(function (b) {
      b.addEventListener('click', function () {
        state.palette = b.getAttribute('data-palette');
        syncControls();
        render();
      });
    });
    var cc = byId('customColor');
    if (cc) {
      cc.addEventListener('input', function () {
        state.customColor = cc.value;
        state.palette = 'custom';
        syncControls();
        render();
      });
    }

    // オプション
    var q = byId('qrCheck');
    if (q) q.addEventListener('change', function () { state.qr = q.checked; render(); });
    var tr2 = byId('bgTransparent');
    if (tr2) tr2.addEventListener('change', function () { state.transparent = tr2.checked; render(); });

    // ボタン
    var pb = byId('printBtn'); if (pb) pb.addEventListener('click', doPrint);
    var pb2 = byId('printBtn2'); if (pb2) pb2.addEventListener('click', doPrint);
    var png = byId('pngBtn'); if (png) png.addEventListener('click', exportPng);
    var sb = byId('sampleBtn'); if (sb) sb.addEventListener('click', fillSample);
    var rb = byId('resetBtn'); if (rb) rb.addEventListener('click', resetForm);
    var lb = byId('langBtn');
    if (lb) lb.addEventListener('click', function () { applyI18n(state.lang === 'ja' ? 'zh' : 'ja'); });

    // シェア
    var xb = byId('shareXBtn');
    if (xb) xb.addEventListener('click', function () {
      openUrl('https://twitter.com/intent/tweet?text=' + encodeURIComponent(shareText()) + '&url=' + encodeURIComponent(SHARE_URL));
    });
    var ln = byId('shareLineBtn');
    if (ln) ln.addEventListener('click', function () {
      openUrl('https://social-plugins.line.me/lineit/share?url=' + encodeURIComponent(SHARE_URL) + '&text=' + encodeURIComponent(shareText()));
    });
    var cp = byId('shareCopyBtn');
    if (cp) cp.addEventListener('click', function () {
      var label = byId('shareCopyLabel');
      var original = label ? label.textContent : '';
      copyText(SHARE_URL).then(function (ok) {
        if (!label) return;
        label.textContent = ok ? tr('copied') : tr('copyFail');
        setTimeout(function () { label.textContent = original || tr('shareCopy'); }, 1800);
      });
    });

    applyI18n('ja');
    syncControls();
    render();
  }

  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', init);
  } else {
    init();
  }

  // テスト用の内部公開（本番の動作には影響しない）
  window.__meishi = {
    buildCardSVG: buildCardSVG,
    QRCode: QRCode,
    state: state,
    render: render,
    buildSheet: buildSheet,
    doPrint: doPrint
  };
})();
