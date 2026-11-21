// Ultra-fast drop-in replacement for make.fun's csv-reader 1.0.0.
// Pure ES module, zero dependencies, deterministic, stateless.

function readUnquotedSlow(text, len, start, crPos, state, errors, recordLine, recordRow) {
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
        state.line += 1;
        ended = 2;
        break;
      }
      if (ch === 13) {
        if (p + 1 < len && text.charCodeAt(p + 1) === 10) {
          if (p > seg) acc += text.slice(seg, p);
          p += 2;
          state.line += 1;
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
  if (ended === 0 && p > seg) {
    acc += text.slice(seg, p);
  }
  state.pos = p;
  state.endedComma = ended === 1;
  return acc;
}

function readQuoteJunk(text, len, p, val, state, errors, recordLine, recordRow) {
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
        state.line += 1;
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
          state.line += 1;
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
  if (added > 0) {
    errors.push({ code: 'quote_junk', line: recordLine, row: recordRow });
  }
  state.pos = p;
  state.endedComma = ended === 1;
  return acc;
}

function readUnterminated(text, len, open, openLine, state, errors, recordLine, recordRow) {
  let p = open + 1;
  state.line = openLine;
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
        state.line += 1;
        ended = 2;
        break;
      }
      if (ch === 13) {
        if (p + 1 < len && text.charCodeAt(p + 1) === 10) {
          if (p > seg) acc += text.slice(seg, p);
          p += 2;
          state.line += 1;
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
  if (ended === 0 && p > seg) {
    acc += text.slice(seg, p);
  }
  state.pos = p;
  state.endedComma = ended === 1;
  return acc;
}

function readQuotedSlow(text, len, open, q, state, errors, recordLine, recordRow) {
  const openLine = state.line;
  if (q === -1) {
    return readUnterminated(text, len, open, openLine, state, errors, recordLine, recordRow);
  }

  let seg = open + 1;
  let acc = '';
  let hasAcc = false;
  let line = openLine;
  let nextLF = state.nextLF;
  let nextCR = state.nextCR;

  while (true) {
    if (nextCR !== -1 && nextCR < q) {
      while (nextCR !== -1 && nextCR < q) {
        while (nextLF !== -1 && nextLF < nextCR) {
          line += 1;
          nextLF = text.indexOf('\n', nextLF + 1);
        }
        acc += text.slice(seg, nextCR) + '\n';
        hasAcc = true;
        line += 1;
        if (nextCR + 1 < len && text.charCodeAt(nextCR + 1) === 10) {
          seg = nextCR + 2;
          if (nextLF === nextCR + 1) nextLF = text.indexOf('\n', seg);
        } else {
          seg = nextCR + 1;
        }
        nextCR = text.indexOf('\r', seg);
      }
    }
    while (nextLF !== -1 && nextLF < q) {
      line += 1;
      nextLF = text.indexOf('\n', nextLF + 1);
    }

    if (q + 1 < len && text.charCodeAt(q + 1) === 34) {
      acc += text.slice(seg, q + 1);
      hasAcc = true;
      seg = q + 2;
      q = text.indexOf('"', seg);
      if (q === -1) {
        state.nextLF = text.indexOf('\n', open + 1);
        state.nextCR = text.indexOf('\r', open + 1);
        return readUnterminated(text, len, open, openLine, state, errors, recordLine, recordRow);
      }
      continue;
    }

    const val = hasAcc ? acc + text.slice(seg, q) : (q === seg ? '' : text.slice(seg, q));
    const p = q + 1;
    state.line = line;
    state.nextLF = nextLF;
    state.nextCR = nextCR;

    if (p >= len) {
      state.pos = p;
      state.endedComma = false;
      return val;
    }
    const next = text.charCodeAt(p);
    if (next === 44) {
      state.pos = p + 1;
      state.endedComma = true;
      return val;
    }
    if (next === 10) {
      state.pos = p + 1;
      state.line = line + 1;
      state.endedComma = false;
      return val;
    }
    if (next === 13 && p + 1 < len && text.charCodeAt(p + 1) === 10) {
      state.pos = p + 2;
      state.line = line + 1;
      state.endedComma = false;
      return val;
    }
    return readQuoteJunk(text, len, p, val, state, errors, recordLine, recordRow);
  }
}

function parseFirstRecord(text, len, state, errors, header) {
  let pos = state.pos;
  let line = state.line;
  let nextLF = state.nextLF;
  let nextCR = state.nextCR;

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
        if (nextLF !== -1 && nextLF < pos + 1) nextLF = text.indexOf('\n', pos + 1);
        if (nextCR !== -1 && nextCR < pos + 1) nextCR = text.indexOf('\r', pos + 1);
        const q = text.indexOf('"', pos + 1);
        state.line = line;
        state.nextLF = nextLF;
        state.nextCR = nextCR;
        const val = readQuotedSlow(text, len, pos, q, state, errors, recordLine, recordRow);
        pos = state.pos;
        line = state.line;
        nextLF = state.nextLF;
        nextCR = state.nextCR;
        fields.push(val);
        if (!state.endedComma) break;
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
            state.line = line;
            const val = readUnquotedSlow(text, len, start, p, state, errors, recordLine, recordRow);
            pos = state.pos;
            line = state.line;
            fields.push(val);
            ended = state.endedComma ? 1 : 2;
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
    state.pos = pos;
    state.line = line;
    state.nextLF = nextLF;
    state.nextCR = nextCR;
    return fields;
  }

  state.pos = pos;
  state.line = line;
  state.nextLF = nextLF;
  state.nextCR = nextCR;
  return null;
}

export function run(input) {
  const text = String(input.text);
  const header = input.header === true;
  const len = text.length;
  const errors = [];
  const rows = [];

  let pos = len > 0 && text.charCodeAt(0) === 0xfeff ? 1 : 0;
  const state = {
    pos,
    line: 1,
    endedComma: false,
    nextLF: text.indexOf('\n', pos),
    nextCR: text.indexOf('\r', pos),
  };

  const first = parseFirstRecord(text, len, state, errors, header);
  if (first === null) {
    return { columns: header ? [] : null, rows, errors };
  }

  const width = first.length;
  const columns = header ? first : null;
  if (!header) rows.push(first);

  pos = state.pos;
  let line = state.line;
  let nextLF = state.nextLF;
  let nextCR = state.nextCR;

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
    const fields = new Array(width);
    let extra = null;
    let fi = 0;
    let lastQuoted = false;
    let needRefresh = true;
    let lineEnd = len;
    let endKind = 0; // 0 = EOF, 1 = LF, 2 = CRLF, 3 = stray CR

    while (true) {
      if (needRefresh) {
        if (nextLF !== -1 && nextLF < pos) nextLF = text.indexOf('\n', pos);
        if (nextCR !== -1 && nextCR < pos) nextCR = text.indexOf('\r', pos);
        lineEnd = nextLF === -1 ? len : nextLF;
        endKind = nextLF === -1 ? 0 : 1;
        if (nextCR !== -1 && nextCR < lineEnd) {
          lineEnd = nextCR;
          endKind = nextCR + 1 === nextLF ? 2 : 3;
        }
        needRefresh = false;
      }

      let val;
      let doneRow = false;

      if (pos < lineEnd) {
        const ch0 = text.charCodeAt(pos);
        if (ch0 !== 34) {
          if (ch0 === 44) {
            lastQuoted = false;
            val = '';
            pos += 1;
          } else {
            let p = pos + 1;
            while (p < lineEnd && text.charCodeAt(p) !== 44) p++;
            if (p < lineEnd) {
              val = text.slice(pos, p);
              pos = p + 1;
            } else if (endKind !== 3) {
              val = text.slice(pos, lineEnd);
              pos = lineEnd + endKind;
              if (endKind !== 0) line += 1;
              doneRow = true;
            } else {
              lastQuoted = false;
              state.line = line;
              val = readUnquotedSlow(text, len, pos, lineEnd, state, errors, recordLine, rows.length);
              pos = state.pos;
              line = state.line;
              if (state.endedComma) needRefresh = true;
              else doneRow = true;
            }
          }
        } else {
          lastQuoted = true;
          const pStart = pos + 1;
          const firstQ = text.indexOf('"', pStart);
          let q = firstQ;
          let fastOk = false;

          if (q !== -1 && q < lineEnd) {
            if (q + 1 < len && text.charCodeAt(q + 1) === 34) {
              let acc = text.slice(pStart, q + 1);
              let seg = q + 2;
              q = text.indexOf('"', seg);
              while (q !== -1 && q < lineEnd && q + 1 < len && text.charCodeAt(q + 1) === 34) {
                acc += text.slice(seg, q + 1);
                seg = q + 2;
                q = text.indexOf('"', seg);
              }
              if (q !== -1 && q < lineEnd) {
                val = q === seg ? acc : acc + text.slice(seg, q);
                fastOk = true;
              }
            } else {
              val = q === pStart ? '' : text.slice(pStart, q);
              fastOk = true;
            }
          }

          if (fastOk) {
            const after = q + 1;
            if (after < lineEnd && text.charCodeAt(after) === 44) {
              pos = after + 1;
            } else if (after === lineEnd && endKind !== 3) {
              pos = lineEnd + endKind;
              if (endKind !== 0) line += 1;
              doneRow = true;
            } else {
              state.line = line;
              val = readQuoteJunk(text, len, after, val, state, errors, recordLine, rows.length);
              pos = state.pos;
              line = state.line;
              if (state.endedComma) needRefresh = true;
              else doneRow = true;
            }
          } else {
            state.line = line;
            state.nextLF = nextLF;
            state.nextCR = nextCR;
            val = readQuotedSlow(text, len, pos, firstQ, state, errors, recordLine, rows.length);
            pos = state.pos;
            line = state.line;
            nextLF = state.nextLF;
            nextCR = state.nextCR;
            if (state.endedComma) needRefresh = true;
            else doneRow = true;
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
          state.line = line;
          val = readUnquotedSlow(text, len, pos, lineEnd, state, errors, recordLine, rows.length);
          pos = state.pos;
          line = state.line;
          if (state.endedComma) needRefresh = true;
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

    if (fi === width) {
      if (fi === 1 && fields[0] === '' && !lastQuoted) continue;
      rows.push(fields);
    } else if (fi === 1 && fields[0] === '' && !lastQuoted) {
      continue;
    } else if (fi < width) {
      errors.push({ code: 'short_row', line: recordLine, row: rows.length, fields: fi });
      for (let i = fi; i < width; i++) fields[i] = '';
      rows.push(fields);
    } else {
      errors.push({ code: 'long_row', line: recordLine, row: rows.length, extra });
      rows.push(fields);
    }
  }

  return { columns, rows, errors };
}

// Pre-seed V8 type feedback (OneByte & TwoByte) on tiny samples to eliminate mid-file Maglev deopts.
{
  const w1 = '\uFEFFa,b\r\n\r\n,1\r\n"","x""y""z"\r\n"ok"j,"m\r\n""n"j\r\n"p"j\r1\r\n\r\r\n1\r\n1,2,3,4\r\n4\r5,6\r7\r\n"u';
  const w2 = 'café,b\n\n,1\n"","x""y"\n"ok"j,"m\rn\n""k"\n1,\n1\n1,2,3,4\n4\r5,6\r7\n"a\nb"';
  const w3 = 'a,b\n1,2\n3,"4"';
  const w4 = 'café,b\r\n"a\nb",1\r\n2,"3\r\n4"';
  for (let i = 0; i < 2; i++) {
    run({ text: w1, header: true });
    run({ text: w2, header: false });
    run({ text: w3, header: true });
    run({ text: w4, header: false });
  }
  run({ text: '', header: true });
}
