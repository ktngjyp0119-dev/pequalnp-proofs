// Run with Node.js 18+ using: node check-cover-two.mjs
// Bit i of a graph mask stands for edge [floor(i / columns), i % columns].
// Each circuit gate is binary. Indices below the input count name inputs;
// later indices name previous gates. The empty circuit reads beyond its inputs.

function ensure(condition, message) {
  if (!condition) throw new Error(message);
}

function graphData(rows, columns, mask) {
  const n = rows + columns;
  const edges = [];
  for (let p = 0; p < rows; p++)
    for (let l = 0; l < columns; l++)
      if (mask & (1 << (p * columns + l))) edges.push([p, rows + l]);
  const active = [...new Set(edges.flat())];
  const degree = Array.from({length: n}, (_, i) => edges.filter(e => e.includes(i)).length);
  const fourCycle = edges.some(([p,l]) => edges.some(([q,m]) =>
    p !== q && l !== m && edges.some(([a,b]) => a === p && b === m) &&
    edges.some(([a,b]) => a === q && b === l)));
  const stars = edges.every(([p,l]) => degree[p] === 1 || degree[l] === 1);
  let cover;
  for (let size = 0; size <= 2 && !cover; size++) {
    for (let s = 0; s < (1 << n); s++) {
      const picked = active.filter(i => s & (1 << i));
      if (picked.length === size && edges.every(e => e.some(i => picked.includes(i)))) {
        cover = picked;
        break;
      }
    }
  }
  return {rows, columns, n, edges, active, fourCycle, stars, cover};
}

function target(g, z) {
  return g.edges.some(([a,b]) => (z & (1 << a)) && (z & (1 << b)));
}

function witness(g) {
  const gates = [];
  if (!g.edges.length) return {gates, out: g.n};
  const stars = g.cover.map(() => []);
  for (const edge of g.edges) {
    const i = g.cover.findIndex(c => edge.includes(c));
    stars[i].push(edge.find(v => v !== g.cover[i]));
  }
  function gate(op, a, b) {
    gates.push([op,a,b]);
    return g.n + gates.length - 1;
  }
  const terms = stars.map((neighbors, i) => {
    ensure(neighbors.length > 0, 'a minimum cover has no redundant center');
    return gate('and', g.cover[i], neighbors.reduce((a,b) => gate('or', a, b)));
  });
  return {gates, out: terms.reduce((a,b) => gate('or', a, b))};
}

function verify(g, c) {
  const wireValues = z => {
    const w = Array.from({length: g.n}, (_,i) => Boolean(z & (1 << i)));
    for (const [op,a,b] of c.gates) {
      ensure(a >= 0 && b >= 0 && a < w.length && b < w.length, 'non-earlier wire');
      w.push(op === 'and' ? w[a] && w[b] : w[a] || w[b]);
    }
    return w;
  };
  for (let z = 0; z < (1 << g.n); z++) {
    const w = wireValues(z);
    ensure((w[c.out] ?? false) === target(g,z), 'wrong output');
    for (let j = 0; j < c.gates.length; j++) {
      if (c.gates[j][0] === 'and' && w[g.n+j]) {
        ensure(target(g,z), 'AND asserted without an edge');
        ensure((z & (z-1)) !== 0, 'AND asserted at a singleton');
      }
    }
  }
}

// Independent synthesis for five inputs: a packed 32-bit truth table per wire.
// Free constant tables relax the lower-bound search. A gate returning an
// available table, including unary and nullary gates, never helps the search.
// Once a state has appeared, any later copy can reuse its shortest construction.
function unrestrictedFive(targetTables) {
  const wires = Array.from({length: 5}, (_,i) => {
    let t = 0;
    for (let z = 0; z < 32; z++) if (z & (1 << i)) t = (t | (1 << z)) >>> 0;
    return t;
  });
  const initial = [0, 0xffffffff, ...wires].sort((a,b) => a-b);
  const best = new Map(initial.filter(t => targetTables.has(t)).map(t => [t,0]));
  let layer = [initial];
  for (let depth = 1; depth <= 5; depth++) {
    const next = new Map();
    for (const state of layer) {
      for (let i = 0; i < state.length; i++)
        for (let j = i + 1; j < state.length; j++)
          for (const v of [(state[i] & state[j]) >>> 0, (state[i] | state[j]) >>> 0]) {
            if (state.includes(v)) continue;
            if (targetTables.has(v) && !best.has(v)) best.set(v, depth);
            if (depth < 5) {
              const s = [...state,v].sort((a,b) => a-b);
              const key = s.join(',');
              if (!next.has(key)) next.set(key,s);
            }
          }
    }
    if (best.size === targetTables.size) break;
    layer = [...next.values()];
  }
  return best;
}

const pack = g => {
  let table = 0;
  for (let z = 0; z < (1 << g.n); z++) if (target(g,z)) table = (table | (1 << z)) >>> 0;
  return table;
};

function check() {
  const small = [];
  for (let mask = 0; mask < 64; mask++) {
    const g = graphData(2,3,mask);
    if (!g.fourCycle) small.push(g);
  }
  const optimal = unrestrictedFive(new Set(small.map(pack)));
  const histogram = Array(6).fill(0);
  for (const g of small) {
    const c = witness(g);
    verify(g,c);
    ensure(optimal.get(pack(g)) === c.gates.length, 'unrestricted optimum differs');
    histogram[c.gates.length]++;
  }
  let cases = 0, nonstars = 0;
  for (let mask = 0; mask < 512; mask++) {
    const g = graphData(3,3,mask);
    if (g.fourCycle || !g.cover) continue;
    const c = witness(g);
    verify(g,c);
    const predicted = g.active.length === 0 ? 0 : g.active.length - Number(g.stars);
    ensure(c.gates.length === predicted, 'wrong predicted size');
    cases++;
    if (!g.stars) nonstars++;
  }
  return {twoByThree: small.length, byMinimum: histogram,
          threeByThreeCoverAtMostTwo: cases, nonstars};
}

// A read-once formula is built by combining two disjoint nonempty sets of leaves.
// For the doubled variant, the last two leaf positions carry the same variable.
const families = new Map();
function formulaTables(k, doubled) {
  const key = k + ':' + doubled;
  if (families.has(key)) return families.get(key);
  const vars = Array.from({length:k}, (_,i) => {
    let value = 0n;
    for (let z=0; z<2**k; z++) if (z & (1<<i)) value |= 1n << BigInt(z);
    return value;
  });
  if (doubled) vars.push(vars[k-1]);
  const end = 1 << vars.length;
  const dp = Array(end);
  for (let s=1; s<end; s++) {
    const out = new Set();
    if ((s & (s-1)) === 0) out.add(vars[31-Math.clz32(s)]);
    else {
      for (let a=(s-1)&s; a; a=(a-1)&s) {
        const b = s^a;
        if (a>=b) continue;
        for (const f of dp[a]) for (const h of dp[b]) {
          out.add(f & h); out.add(f | h);
        }
      }
    }
    dp[s] = out;
  }
  families.set(key,dp[end-1]);
  return dp[end-1];
}

function packed(k, f) {
  let table = 0n;
  for (let z=0; z < 2**k; z++) if (f(z)) table |= 1n << BigInt(z);
  return table;
}

function scatter(bits, positions) {
  return positions.reduce((out,p,i) => out | (((bits >> i)&1) << p),0);
}

function canUseOneFork(n, f) {
  const all = Array.from({length:n}, (_,i) => i);
  for (let s=1; s<(1<<n); s++) {
    const part = all.filter(i => s & (1<<i));
    const rest = all.filter(i => !(s & (1<<i)));
    const full = (1n << BigInt(2**part.length)) - 1n;
    let inner;
    let compatible = true;
    for (let z=0; z<(1<<rest.length); z++) {
      const outside = scatter(z,rest);
      const slice = packed(part.length,t => f(outside|scatter(t,part)));
      if (slice === 0n || slice === full) continue;
      if (inner === undefined) inner = slice;
      else if (inner !== slice) { compatible = false; break; }
    }
    if (!compatible || inner === undefined || !formulaTables(part.length,false).has(inner)) continue;
    const outer = packed(rest.length+1, z =>
      f(scatter(z,rest) | ((z & (1<<rest.length)) ? s : 0)));
    if (formulaTables(rest.length+1,true).has(outer)) return true;
  }
  return false;
}

function checkAllThree() {
  const exact = Array(9).fill(0), open = [];
  let graphCount = 0;
  for (let mask=0; mask<512; mask++) {
    const g = graphData(3,3,mask);
    if (g.fourCycle) continue;
    graphCount++;
    // All three vertices on the left cover the edges. When three are needed,
    // each has a neighbor, so the witness routine uses all three centers.
    if (!g.cover) g.cover = [0,1,2];
    const c = witness(g);
    verify(g,c);
    const v = g.active.length;
    if (!v) { exact[0]++; continue; }
    const f = z => target(g,scatter(z,g.active));
    let lower = v-1;
    if (!formulaTables(v,false).has(packed(v,f))) {
      lower++;
      if (lower < c.gates.length && !canUseOneFork(v,f)) lower++;
    }
    if (lower > c.gates.length) throw Error('inconsistent bounds');
    if (lower === c.gates.length) exact[lower]++;
    else open.push({mask,lower,upper:c.gates.length});
  }
  return {graphCount, exact, open};
}

// Decide whether a formula with exactly these leaf occurrences can realize
// the specified truth table. At the final operation the target constrains
// both children, so the largest table family need not be materialized.
function formulaExists(leaves,target) {
  const end = (1 << leaves.length)-1, memo = new Map();
  function values(mask) {
    if (memo.has(mask)) return memo.get(mask);
    const out = new Set();
    if ((mask & (mask-1)) === 0) out.add(leaves[31-Math.clz32(mask)]);
    else for (let a=(mask-1)&mask;a;a=(a-1)&mask) {
      const b=a^mask;
      if (a>=b) continue;
      for (const u of values(a)) for (const v of values(b)) {
        out.add(u & v); out.add(u | v);
      }
    }
    memo.set(mask,out);
    return out;
  }
  if (leaves.length === 1) return leaves[0] === target;
  for (let a=(end-1)&end;a;a=(a-1)&end) {
    const b=end^a;
    if (a>=b) continue;
    const left=values(a),right=values(b);
    const cover=[], covered=[];
    for (const v of right) {
      if ((v & target) === target) cover.push(v);
      if ((v | target) === target) covered.push(v);
    }
    for (const u of left) {
      if ((u & target) === target && cover.some(v=>(u & v)===target)) return true;
      if ((u | target) === target && covered.some(v=>(u | v)===target)) return true;
    }
  }
  return false;
}

function sixCycle() {
  // Vertices in cyclic order make repeated-leaf cases fall into distance orbits.
  const f = z => [0,1,2,3,4,5].some(i => (z & (1<<i)) && (z & (1<<((i+1)%6))));
  const inputs=Array.from({length:6},(_,i)=>packed(6,z=>z & (1<<i)));
  const targetTable=packed(6,f);
  const repeatedLeaf = [0,1,2,3].map(d => formulaExists([...inputs,inputs[0],inputs[d]], targetTable));

  // At most two excess uses (fan-outs counted with multiplicity).
  // If a first internally reused gate has exclusive inputs, all nonconstant
  // sections on that block must agree. Test this for every proper block.
  const all=[0,1,2,3,4,5];
  function slicesAgree(block) {
    const rest=all.filter(i=>!block.includes(i));
    let fixed;
    const ones=(1n<<BigInt(1<<block.length))-1n;
    for (let t=0;t<(1<<rest.length);t++) {
      const o=scatter(t,rest);
      const v=packed(block.length,b=>f(o|scatter(b,block)));
      if (v===0n || v===ones) continue;
      if (fixed!==undefined && fixed!==v) return false;
      fixed=v;
    }
    return true;
  }
  const exclusive=[];
  for (let mask=1;mask<63;mask++) {
    const block=all.filter(i=>mask & (1<<i));
    if (block.length>=2 && slicesAgree(block)) exclusive.push(mask);
  }
  // Last possibility: one input is used both inside and outside the only
  // shared gate. Rotate that input to vertex zero. Other inputs are exclusive.
  let innerOptions=0, compatibleOptions=0;
  for (let mask=1;mask<32;mask++) {
    const privateInputs=all.slice(1).filter(i=>mask & (1<<(i-1)));
    const block=[0,...privateInputs], outerInputs=all.filter(i=>!block.includes(i));
    // For fixed x_0, any nonconstant private-input section must equal the
    // corresponding restriction of the inner formula.
    const constraints=[];
    for (let x=0;x<=1;x++) for(let b=0;b<1<<outerInputs.length;b++) {
      const o=x|scatter(b,outerInputs);
      const want=packed(privateInputs.length,z=>f(o|scatter(z,privateInputs)));
      const ones=(1n<<BigInt(1<<privateInputs.length))-1n;
      if (want!==0n && want!==ones) constraints.push([x,want]);
    }
    for (const candidate of formulaTables(block.length,false)) {
      innerOptions++;
      if (!constraints.every(([x,want])=>packed(privateInputs.length,z=>
        Boolean((candidate >> BigInt(2*z+x)) & 1n))===want)) continue;
      compatibleOptions++;
      const inner=packed(6,z=>{
        const index=block.reduce((acc,p,i)=>acc|(((z>>p)&1)<<i),0);
        return Boolean((candidate >> BigInt(index)) & 1n);
      });
      if (formulaExists([inputs[0],...outerInputs.map(i=>inputs[i]),inner,inner],targetTable))
        return {repeatedLeaf,exclusive,sharedInputAndGate:true,innerOptions,compatibleOptions};
    }
  }
  return {repeatedLeaf,exclusive,sharedInputAndGate:false,innerOptions,compatibleOptions};

}

function audit() {
  const small = check();
  const search = checkAllThree();
  const cycle = sixCycle();
  if (cycle.repeatedLeaf.some(Boolean) || cycle.exclusive.length || cycle.sharedInputAndGate) {
    throw Error('the six-cycle lower bound did not close');
  }
  if (search.open.length !== 6) throw Error('unexpected frontier');
  for (const {mask,lower,upper} of search.open) {
    const g=graphData(3,3,mask);
    if (lower!==7 || upper!==8 || g.edges.length!==6 ||
        !Array.from({length:6},(_,v)=>g.edges.filter(e=>e.includes(v)).length===2).every(Boolean))
      throw Error('an unresolved graph is not a six-cycle with the expected bounds');
    search.exact[8]++;
  }
  if (search.exact.reduce((a,b)=>a+b,0) !== search.graphCount) throw Error('missing graphs');
  // Cross-check the two structural lower-bound searches on five inputs
  // against independent unrestricted synthesis, including positive cases.
  const graphs=Array.from({length:64},(_,m)=>graphData(2,3,m)).filter(g=>!g.fourCycle);
  const best=unrestrictedFive(new Set(graphs.map(pack)));
  for(const g of graphs) {
    const v=g.active.length;
    if (!v) continue;
    const f=z=>target(g,scatter(z,g.active)), optimum=best.get(pack(g));
    const ro=formulaTables(v,false).has(packed(v,f));
    if (ro !== (optimum === v-1)) throw Error('read-once cross-check failed');
    if (!ro && canUseOneFork(v,f) !== (optimum===v)) throw Error('one-fork cross-check failed');
  }
  const inputs=Array.from({length:4},(_,i)=>packed(4,z=>z & (1<<i)));
  const [a,b,c,d]=inputs;
  if (!formulaExists([...inputs,a],(a&b)|((a|c)&d))) throw Error('positive formula control failed');
  return {twoByThree:small,threeByThree:{cases:search.graphCount,optimumHistogram:search.exact},
    sixCycle:cycle};
}

console.log(JSON.stringify(audit(), null, 2));
