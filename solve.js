// Ultra-fast drop-in replacement for make.fun's csv-reader 1.0.0.
// Pure ES module, zero dependencies, deterministic, stateless.
// Optimized for Node 22 / V8 TurboFan: chunked body parser (eliminates OSR
// double-compilation), lazy nextLF/nextCR/nextComma SIMD indexOf tracking,
// single-line quoted fast path, and zero-deopt cold-helper separation.

let gPos = 0;
let gLine = 1;
let gEndedComma = false;
let gNextLF = -1;
let gNextCR = -1;
let gNextComma = -1;

function readUnquotedSlow(text, len, start, crPos, line, errors, recordLine, recordRow) {
  let acc = text.slice(start, crPos);
  errors.push({ code: 'stray_cr', line: recordLine, row: recordRow });
  let p = crPos + 1;
  let seg = p;
  let ended = 0;

  while (p < len) {
    const ch = text.charCodeAt(p);
    if (ch <= 44) {
      if (ch === 44) {
        if (p > seg) acc += text.slice(seg, p);
        p += 1;
        ended = 1;
        break;
      }
      if (ch === 10) {
        if (p > seg) acc += text.slice(seg, p);
        p += 1;
        line += 1;
        ended = 2;
        break;
      }
      if (ch === 13) {
        if (p + 1 < len && text.charCodeAt(p + 1) === 10) {
          if (p > seg) acc += text.slice(seg, p);
          p += 2;
          line += 1;
          ended = 2;
          break;
        }
        if (p > seg) acc += text.slice(seg, p);
        errors.push({ code: 'stray_cr', line: recordLine, row: recordRow });
        p += 1;
        seg = p;
        continue;
      }
    }
    p += 1;
  }
  if (ended === 0 && p > seg) acc += text.slice(seg, p);
  gPos = p;
  gLine = line;
  gEndedComma = ended === 1;
  return acc;
}

function readQuoteJunk(text, len, p, val, line, errors, recordLine, recordRow) {
  let acc = val;
  let seg = p;
  let added = 0;
  let ended = 0;

  while (p < len) {
    const ch = text.charCodeAt(p);
    if (ch <= 44) {
      if (ch === 44) {
        if (p > seg) {
          acc += text.slice(seg, p);
          added += p - seg;
        }
        p += 1;
        ended = 1;
        break;
      }
      if (ch === 10) {
        if (p > seg) {
          acc += text.slice(seg, p);
          added += p - seg;
        }
        p += 1;
        line += 1;
        ended = 2;
        break;
      }
      if (ch === 13) {
        if (p + 1 < len && text.charCodeAt(p + 1) === 10) {
          if (p > seg) {
            acc += text.slice(seg, p);
            added += p - seg;
          }
          p += 2;
          line += 1;
          ended = 2;
          break;
        }
        if (p > seg) {
          acc += text.slice(seg, p);
          added += p - seg;
        }
        errors.push({ code: 'stray_cr', line: recordLine, row: recordRow });
        p += 1;
        seg = p;
        continue;
      }
    }
    p += 1;
  }
  if (ended === 0 && p > seg) {
    acc += text.slice(seg, p);
    added += p - seg;
  }
  if (added > 0) errors.push({ code: 'quote_junk', line: recordLine, row: recordRow });
  gPos = p;
  gLine = line;
  gEndedComma = ended === 1;
  return acc;
}

function readUnterminated(text, len, open, openLine, errors, recordLine, recordRow) {
  let p = open + 1;
  let line = openLine;
  errors.push({ code: 'unterminated_quote', line: recordLine, row: recordRow });
  let acc = '"';
  let seg = p;
  let ended = 0;

  while (p < len) {
    const ch = text.charCodeAt(p);
    if (ch <= 44) {
      if (ch === 44) {
        if (p > seg) acc += text.slice(seg, p);
        p += 1;
        ended = 1;
        break;
      }
      if (ch === 10) {
        if (p > seg) acc += text.slice(seg, p);
        p += 1;
        line += 1;
        ended = 2;
        break;
      }
      if (ch === 13) {
        if (p + 1 < len && text.charCodeAt(p + 1) === 10) {
          if (p > seg) acc += text.slice(seg, p);
          p += 2;
          line += 1;
          ended = 2;
          break;
        }
        if (p > seg) acc += text.slice(seg, p);
        errors.push({ code: 'stray_cr', line: recordLine, row: recordRow });
        p += 1;
        seg = p;
        continue;
      }
    }
    p += 1;
  }
  if (ended === 0 && p > seg) acc += text.slice(seg, p);
  gPos = p;
  gLine = line;
  gEndedComma = ended === 1;
  return acc;
}

function readQuotedComplex(text, len, open, q, lineEnd, line, errors, recordLine, recordRow) {
  const openLine = line;
  if (q === -1) return readUnterminated(text, len, open, openLine, errors, recordLine, recordRow);

  let seg = open + 1;
  let acc = '';
  let hasAcc = false;

  while (true) {
    if (q >= lineEnd) {
      let p = seg;
      while (p < q) {
        const ch = text.charCodeAt(p);
        if (ch <= 13) {
          if (ch === 10) {
            line += 1;
          } else if (ch === 13) {
            acc += text.slice(seg, p) + '\n';
            hasAcc = true;
            line += 1;
            if (p + 1 < q && text.charCodeAt(p + 1) === 10) p += 1;
            seg = p + 1;
          }
        }
        p += 1;
      }
    }

    if (q + 1 < len && text.charCodeAt(q + 1) === 34) {
      acc += text.slice(seg, q + 1);
      hasAcc = true;
      seg = q + 2;
      q = text.indexOf('"', seg);
      if (q === -1) return readUnterminated(text, len, open, openLine, errors, recordLine, recordRow);
      continue;
    }

    const val = hasAcc ? (q === seg ? acc : acc + text.slice(seg, q)) : (q === seg ? '' : text.slice(seg, q));
    const after = q + 1;
    if (after >= len) {
      gPos = after;
      gLine = line;
      gEndedComma = false;
      return val;
    }
    const next = text.charCodeAt(after);
    if (next === 44) {
      gPos = after + 1;
      gLine = line;
      gEndedComma = true;
      return val;
    }
    if (next === 10) {
      gPos = after + 1;
      gLine = line + 1;
      gEndedComma = false;
      return val;
    }
    if (next === 13 && after + 1 < len && text.charCodeAt(after + 1) === 10) {
      gPos = after + 2;
      gLine = line + 1;
      gEndedComma = false;
      return val;
    }
    return readQuoteJunk(text, len, after, val, line, errors, recordLine, recordRow);
  }
}

function finishAbnormalRow(fields, fi, width, lastQuoted, extra, recordLine, rows, errors) {
  if (fi === 1 && fields[0] === '' && !lastQuoted) return;
  if (fi < width) {
    errors.push({ code: 'short_row', line: recordLine, row: rows.length, fields: fi });
    for (let i = fi; i < width; i++) fields[i] = '';
    rows.push(fields);
  } else {
    errors.push({ code: 'long_row', line: recordLine, row: rows.length, extra });
    rows.push(fields);
  }
}

function parseFirstRecord(text, len, errors, header) {
  let pos = gPos;
  let line = gLine;

  while (pos < len) {
    const c0 = text.charCodeAt(pos);
    if (c0 === 10) {
      pos += 1;
      line += 1;
      continue;
    }
    if (c0 === 13 && pos + 1 < len && text.charCodeAt(pos + 1) === 10) {
      pos += 2;
      line += 1;
      continue;
    }

    const recordLine = line;
    const recordRow = header ? null : 0;
    const fields = [];
    let lastQuoted = false;

    while (true) {
      if (pos < len && text.charCodeAt(pos) === 34) {
        lastQuoted = true;
        fields.push(readQuotedComplex(text, len, pos, text.indexOf('"', pos + 1), -1, line, errors, recordLine, recordRow));
        pos = gPos;
        line = gLine;
        if (!gEndedComma) break;
        continue;
      }

      lastQuoted = false;
      const start = pos;
      let p = pos;
      let ended = 0;
      while (p < len) {
        const ch = text.charCodeAt(p);
        if (ch <= 44) {
          if (ch === 44) {
            fields.push(p === start ? '' : text.slice(start, p));
            pos = p + 1;
            ended = 1;
            break;
          }
          if (ch === 10) {
            fields.push(p === start ? '' : text.slice(start, p));
            pos = p + 1;
            line += 1;
            ended = 2;
            break;
          }
          if (ch === 13) {
            if (p + 1 < len && text.charCodeAt(p + 1) === 10) {
              fields.push(p === start ? '' : text.slice(start, p));
              pos = p + 2;
              line += 1;
              ended = 2;
              break;
            }
            fields.push(readUnquotedSlow(text, len, start, p, line, errors, recordLine, recordRow));
            pos = gPos;
            line = gLine;
            ended = gEndedComma ? 1 : 2;
            break;
          }
        }
        p += 1;
      }
      if (ended === 0) {
        fields.push(p === start ? '' : text.slice(start, p));
        pos = len;
        break;
      }
      if (ended === 2) break;
    }

    if (fields.length === 1 && fields[0] === '' && !lastQuoted) continue;
    gPos = pos;
    gLine = line;
    return fields;
  }

  gPos = pos;
  gLine = line;
  return null;
}

function parseChunk(text, len, width, rows, errors, limit) {
  let pos = gPos;
  let line = gLine;
  let nextLF = gNextLF;
  let nextCR = gNextCR;
  let nextComma = gNextComma;
  let count = 0;

  while (pos < len && count < limit) {
    const c0 = text.charCodeAt(pos);
    if (c0 === 10) {
      pos += 1;
      line += 1;
      continue;
    }
    if (c0 === 13 && pos + 1 < len && text.charCodeAt(pos + 1) === 10) {
      pos += 2;
      line += 1;
      continue;
    }

    count += 1;
    const recordLine = line;
    const fields = new Array(width);
    let extra = null;
    let fi = 0;
    let lastQuoted = false;
    let lineEnd = -1;
    let endKind = 0; // 0 = EOF, 1 = LF, 2 = CRLF, 3 = stray CR

    while (true) {
      if (lineEnd < 0) {
        if (nextLF !== -1 && nextLF < pos) nextLF = text.indexOf('\n', pos);
        if (nextCR !== -1 && nextCR < pos) nextCR = text.indexOf('\r', pos);
        lineEnd = nextLF === -1 ? len : nextLF;
        endKind = nextLF === -1 ? 0 : 1;
        if (nextCR !== -1 && nextCR < lineEnd) {
          lineEnd = nextCR;
          endKind = nextCR + 1 === nextLF ? 2 : 3;
        }
      }

      let val;
      let doneRow = false;

      if (pos < lineEnd) {
        const ch0 = text.charCodeAt(pos);
        if (ch0 !== 34) {
          if (ch0 === 44) {
            val = '';
            pos += 1;
          } else {
            if (nextComma !== -1 && nextComma < pos) nextComma = text.indexOf(',', pos + 1);
            if (nextComma !== -1 && nextComma < lineEnd) {
              val = text.slice(pos, nextComma);
              pos = nextComma + 1;
            } else if (endKind !== 3) {
              val = text.slice(pos, lineEnd);
              pos = lineEnd + endKind;
              if (endKind !== 0) line += 1;
              doneRow = true;
            } else {
              lastQuoted = false;
              val = readUnquotedSlow(text, len, pos, lineEnd, line, errors, recordLine, rows.length);
              pos = gPos;
              line = gLine;
              if (gEndedComma) lineEnd = -1;
              else doneRow = true;
            }
          }
        } else {
          lastQuoted = true;
          const pStart = pos + 1;
          const q = text.indexOf('"', pStart);
          const after = q + 1;
          if (q !== -1 && q < lineEnd && after < lineEnd && text.charCodeAt(after) === 44) {
            val = q === pStart ? '' : text.slice(pStart, q);
            pos = after + 1;
          } else if (q !== -1 && after === lineEnd && endKind !== 3) {
            val = q === pStart ? '' : text.slice(pStart, q);
            pos = lineEnd + endKind;
            if (endKind !== 0) line += 1;
            doneRow = true;
          } else {
            val = readQuotedComplex(text, len, pos, q, lineEnd, line, errors, recordLine, rows.length);
            pos = gPos;
            line = gLine;
            if (gEndedComma) {
              if (pos > lineEnd) lineEnd = -1;
            } else {
              doneRow = true;
            }
          }
        }
      } else {
        lastQuoted = false;
        if (endKind !== 3) {
          val = '';
          pos = lineEnd + endKind;
          if (endKind !== 0) line += 1;
          doneRow = true;
        } else {
          val = readUnquotedSlow(text, len, pos, lineEnd, line, errors, recordLine, rows.length);
          pos = gPos;
          line = gLine;
          if (gEndedComma) lineEnd = -1;
          else doneRow = true;
        }
      }

      if (fi < width) {
        fields[fi] = val;
      } else if (extra === null) {
        extra = [val];
      } else {
        extra.push(val);
      }
      fi += 1;
      if (doneRow) break;
    }

    if (fi === width && (width > 1 || fields[0] !== '' || lastQuoted)) {
      rows.push(fields);
    } else {
      finishAbnormalRow(fields, fi, width, lastQuoted, extra, recordLine, rows, errors);
    }
  }

  gPos = pos;
  gLine = line;
  gNextLF = nextLF;
  gNextCR = nextCR;
  gNextComma = nextComma;
}

export function run(input) {
  const text = String(input.text);
  const header = input.header === true;
  const len = text.length;
  const errors = [];
  const rows = [];

  gPos = len > 0 && text.charCodeAt(0) === 0xfeff ? 1 : 0;
  gLine = 1;
  gEndedComma = false;

  const first = parseFirstRecord(text, len, errors, header);
  if (first === null) {
    return { columns: header ? [] : null, rows, errors };
  }

  const width = first.length;
  const columns = header ? first : null;
  if (!header) rows.push(first);

  gNextLF = text.indexOf('\n', gPos);
  gNextCR = text.indexOf('\r', gPos);
  gNextComma = text.indexOf(',', gPos);

  while (gPos < len) {
    parseChunk(text, len, width, rows, errors, 512);
  }

  return { columns, rows, errors };
}

// Pre-seed V8 type feedback (OneByte & TwoByte, LF/CRLF/no-CR/stray-CR/quoted/abnormal rows)
// to prevent mid-file TurboFan eager deopts.
{
  const wCRLF = '\uFEFFa,b\r\n\r\n,1\r\n"","x""y""z"\r\n"ok"j,"m\r\n""n"j\r\n"p"j\r1\r\n\r\r\n1\r\n1,2,3,4\r\n4\r5,6\r7\r\n\r,9\r\n"u';
  const wLF = 'café,b\n\n,1\n"","x""y""z"\n"ok"j,"m\n\rn\n""k"j\n"q"\rj\n"z"\r,2\n1,\n1\n1,2,3,4\n4\r5,6\r7\n"a\nb"j,1\n"x""y';
  const wNoCR = 'café,b\n1,2\n3,"4"\n"5"x,6\n"7"y\n"a\nb",c';
  const w1 = 'a\n""\n\r\n\r\r\nb\n1,2,3\n';
  for (let i = 0; i < 3; i++) {
    run({ text: wCRLF, header: true });
    run({ text: wLF, header: false });
    run({ text: wNoCR, header: true });
    run({ text: w1, header: false });
  }
  run({ text: '', header: true });
}
