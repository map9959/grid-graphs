//! Coupled physical strip constraints. No lists of crossing ports or port caps.
use std::collections::{HashMap, HashSet};
use std::io::{self, Read};
type Word = u64;
type Dom = usize;
const BAD: u32 = u32::MAX;

#[derive(Clone, Copy, Eq, PartialEq, Hash)]
struct Forest {
    old: u16,
    part: u64,
    mark: u16,
    open: u16,
}
impl Forest {
    fn base(n: usize) -> Self {
        Self {
            old: 65535,
            part: (0..=n).map(|i| (i as u64) << (4 * i)).sum(),
            mark: 0,
            open: 1 << n,
        }
    }
}
struct UF {
    p: [usize; 32],
    f: [u8; 32],
}
impl UF {
    fn root(&self, mut i: usize) -> usize {
        while self.p[i] != i {
            i = self.p[i]
        }
        i
    }
    fn edge(&mut self, i: usize, j: usize) -> bool {
        let a = self.root(i);
        let b = self.root(j);
        if a == b {
            return false;
        }
        self.p[a] = b;
        self.f[b] |= self.f[a];
        true
    }
}
fn row(s: Forest, n: usize, m: u16, teeth: u16, exits: u16) -> Option<Forest> {
    let mut u = UF {
        p: [0; 32],
        f: [0; 32],
    };
    for i in 0..=n {
        u.p[i] = ((s.part >> (4 * i)) & 15) as usize;
        u.f[i] = (((s.mark >> i) & 1) * 2 + ((s.open >> i) & 1)) as u8;
    }
    for i in 0..n {
        let j = n + 1 + i;
        u.p[j] = j;
        u.f[j] = (((m >> i) & 1) * 2 + ((exits >> i) & 1)) as u8;
        if s.old != 65535 && ((s.old | m) >> i) & 1 != 0 && !u.edge(i, j) {
            return None;
        }
        if i > 0 && (m >> (i - 1)) & 3 != 0 && !u.edge(j - 1, j) {
            return None;
        }
        if m & teeth & (1 << i) != 0 && !u.edge(j, n) {
            return None;
        }
    }
    let mut ids = [32; 32];
    let mut t = Forest {
        old: m,
        part: 0,
        mark: 0,
        open: 0,
    };
    for i in 0..=n {
        let a = u.root(if i == n { n } else { n + 1 + i });
        if ids[a] == 32 {
            ids[a] = i;
            if u.f[a] & 2 != 0 {
                t.mark |= 1 << i
            }
            if u.f[a] & 1 != 0 {
                t.open |= 1 << i
            }
        }
        t.part |= (ids[a] as u64) << (4 * i);
    }
    for i in 0..n {
        if u.p[i] == i && ids[i] == 32 && u.f[i] == 2 {
            return None;
        }
    }
    Some(t)
}
#[derive(Default)]
struct Dict<T: Eq + std::hash::Hash + Clone> {
    items: Vec<T>,
    ids: HashMap<T, usize>,
}
impl<T: Eq + std::hash::Hash + Clone> Dict<T> {
    fn new() -> Self {
        Self {
            items: Vec::new(),
            ids: HashMap::new(),
        }
    }
    fn id(&mut self, v: T) -> usize {
        if let Some(i) = self.ids.get(&v) {
            return *i;
        }
        let i = self.items.len();
        self.items.push(v.clone());
        self.ids.insert(v, i);
        i
    }
}
fn slice(w: Word, i: usize) -> Word {
    (w >> (9 * i)) & 511
}
fn pq(w: Word, y: Word, i: usize, hor: bool) -> Word {
    let (a, b, c, d) = (slice(w, i), slice(y, i), slice(w, i + 1), slice(y, i + 1));
    if hor {
        a | c << 9 | b << 18 | d << 27
    } else {
        a | b << 9 | c << 18 | d << 27
    }
}
fn account(
    k: usize,
    grid: &[usize],
    dom: &Dict<Vec<Word>>,
    gx: &[usize],
    gy: &[usize],
    block: usize,
) {
    // Independent repetition counts per block. Include each end tile
    // twice in that coordinate, so the sum prices four copies of D.
    let mut cs = vec![vec![(0u64, 0u64); gy.len() + 1]; gx.len() + 1];
    for y in 0..k - 1 {
        for x in 0..k - 1 {
            let vals = dom.items[grid[y * (k - 1) + x]].iter().map(|p| {
                (0..4)
                    .map(|s| {
                        let a = 1 + ((s / 2 == 0 && x == 0) || (s / 2 == 1 && x == k - 2)) as u64;
                        let b = 1 + ((s % 2 == 0 && y == 0) || (s % 2 == 1 && y == k - 2)) as u64;
                        a * b * (3 - slice(*p, s).count_ones() as u64)
                    })
                    .sum::<u64>()
            });
            let lo = vals.clone().min().unwrap();
            let hi = vals.max().unwrap();
            for u in 0..=gx.len() {
                if u != 0 && !(gx[u - 1] <= x && x < gx[u - 1] + block) {
                    continue;
                }
                for v in 0..=gy.len() {
                    if v != 0 && !(gy[v - 1] <= y && y < gy[v - 1] + block) {
                        continue;
                    }
                    cs[u][v].0 += lo;
                    cs[u][v].1 += hi;
                }
            }
        }
    }
    println!("4D coefficient bounds {:?}", cs)
}
struct Engine {
    k: usize,
    stride:usize,
    open_north:bool,
    open_south:bool,
    sealed:bool,
    trunk:u16,
    rootfrom:Option<usize>,
    h: usize,
    hor: bool,
    edge: u8,
    q: Option<usize>,
    omit: u16,
    forest: Dict<Forest>,
    step: HashMap<(u32, Word, u8), u32>,
    jt: HashMap<Vec<Dom>, usize>,
    tabs: Vec<HashMap<Word, Vec<Word>>>,
    sets: Dict<Vec<(Word, u32)>>,
    fwd: HashMap<(usize, usize, u8), usize>,
    back: HashMap<(usize, usize, usize, u8), (usize, Vec<Dom>)>,
}
impl Engine {
    fn new(k: usize, h: usize, hor: bool, edge: u8, q: Option<usize>, omit: u16) -> Self {
        let mut e = Self {
            k,
            stride:k-1,open_north:false,open_south:false,sealed:false,trunk:0,rootfrom:None,
            h,
            hor,
            edge,
            q,
            omit,
            forest: Dict::new(),
            step: HashMap::new(),
            jt: HashMap::new(),
            tabs: vec![],
            sets: Dict::new(),
            fwd: HashMap::new(),
            back: HashMap::new(),
        };
        e.forest.id(Forest::base(3 * h));
        e
    }
    fn stage(&self, j: usize) -> u8 {
        let open0=j==0 && self.open_north;
        let open1=j+1==self.k && self.open_south;
        ((j == 0 || j + 1 == self.k) && !open0 && !open1) as u8
            + 2 * ((self.omit != 0 && (if self.hor { self.q == Some(j) } else { j == 0 })) as u8)
            +4*(open0 as u8)+8*(open1 as u8)+16*(self.rootfrom.map_or(false,|f|j>=f) as u8)
    }
    fn advance(&mut self, s: u32, w: Word, stage: u8) -> u32 {
        if let Some(u) = self.step.get(&(s, w, stage)) {
            return *u;
        }
        let n = 3 * self.h;
        let mut t = Some(self.forest.items[s as usize]);
        let exits = if self.edge & 1 == 0 { 1 } else { 0 }
            | if self.edge & 2 == 0 { 1 << (n - 1) } else { 0 };
        let rim = if self.edge & 1 != 0 { 2 } else { 0 }
            | if self.edge & 2 != 0 { 1 << (n - 2) } else { 0 };
        for b in 0..3 {
            let mut m = 0;
            for i in 0..n {
                let bit = if self.hor {
                    3 * b + i % 3
                } else {
                    3 * (i % 3) + b
                };
                m |= (((slice(w, i / 3) >> bit) & 1) as u16) << i;
            }
            let mut tooth = if b == 1 && stage & 1 != 0 {
                (1 << n) - 1
            } else {
                rim
            };
            if b == 1 && stage & 2 != 0 {
                tooth &= !self.omit
            }
            if b==1 && stage&4!=0{tooth|=self.trunk}
            if stage&16!=0{tooth|=2}
            let open=(b==0 && stage&4!=0 && !self.sealed)||(b==2 && stage&8!=0);
            t = t.and_then(|s| row(s, n, m, tooth, if open{(1<<n)-1}else{exits}));
        }
        let u = t.map(|x| self.forest.id(x) as u32).unwrap_or(BAD);
        self.step.insert((s, w, stage), u);
        u
    }
    fn table(&mut self, ds: Vec<Dom>, dom: &Dict<Vec<Word>>) -> usize {
        if let Some(i) = self.jt.get(&ds) {
            return *i;
        }
        let mut edges = vec![(0, 0)];
        for (i, d) in ds.iter().enumerate() {
            let mut lookup = HashMap::<(Word, Word), Vec<(Word, Word)>>::new();
            for p in &dom.items[*d] {
                let (a, b, c, z) = (slice(*p, 0), slice(*p, 1), slice(*p, 2), slice(*p, 3));
                let (b, c) = if self.hor { (c, b) } else { (b, c) };
                lookup.entry((a, b)).or_default().push((c, z));
            }
            let mut ne = vec![];
            if i == 0 {
                for ((a, b), cs) in lookup {
                    for (c, z) in cs {
                        ne.push((a | (c << 9), b | (z << 9)))
                    }
                }
            } else {
                for (w, y) in edges {
                    if let Some(cs) = lookup.get(&(slice(w, i), slice(y, i))) {
                        for &(c, z) in cs {
                            ne.push((w | c << (9 * (i + 1)), y | z << (9 * (i + 1))))
                        }
                    }
                }
            }
            edges = ne;
        }
        let mut tab = HashMap::<Word, Vec<Word>>::new();
        for (w, y) in edges {
            tab.entry(w).or_default().push(y)
        }
        let id = self.tabs.len();
        self.tabs.push(tab);
        self.jt.insert(ds, id);
        id
    }
    // Insert zero or more groups of `period` real transitions. The
    // phase is on the path length, never on the masks or forest labels.
    fn close(
        &mut self,
        start: usize,
        ts: &[usize],
        period: usize,
        minimum: usize,
        stage:u8,
    ) -> (usize, Vec<(u64, u64, Word, Word, usize)>) {
        // Store state indices (words can be wider than 32 bits).
        let mut ids = HashMap::new();
        let mut states = vec![];
        let mut todo = vec![];
        let mut visited = HashSet::new();
        for p in self.sets.items[start].clone() {
            let n = states.len();
            ids.insert(p, n);
            states.push(p);
            visited.insert((n, 0usize));
            todo.push((n, 0usize));
        }
        let acc = minimum * period;
        let phases = acc + period;
        let mut arcs = vec![];
        let mut ok = vec![];
        let mut i = 0;
        while i < todo.len() {
            let (s, phase) = todo[i];
            i += 1;
            let (w, z) = states[s];
            if phase == acc {
                ok.push((w, z))
            }
            let t = ts[phase % ts.len()];
            if let Some(ys) = self.tabs[t].get(&w).cloned() {
                for y in ys {
                    let g = self.advance(z, y, stage);
                    if g == BAD {
                        continue;
                    }
                    let p = (y, g);
                    let id = *ids.entry(p).or_insert_with(|| {
                        let j = states.len();
                        states.push(p);
                        j
                    });
                    let next = (id, if phase + 1 == phases { acc } else { phase + 1 });
                    if visited.insert(next) {
                        todo.push(next)
                    }
                    arcs.push((
                        (s * phases + phase) as u64,
                        (id * phases + next.1) as u64,
                        w,
                        y,
                        phase % ts.len(),
                    ));
                }
            }
        }
        // The reverse search below needs state identities at phase zero.
        // Map those nodes to IDs of singleton frontier sets, using a
        // disjoint tag from internal phase nodes.
        let mut tags = vec![];
        for &p in &states {
            tags.push(self.sets.id(vec![p]) as u64)
        }
        let name = |v: u64| {
            let p = v as usize % phases;
            let id = v as usize / phases;
            if p == acc {
                tags[id] << 2
            } else if p == 0 {
                (tags[id] << 2) | 1
            } else {
                (v << 2) | 2
            }
        };
        for (a, b, _, _, _) in &mut arcs {
            *a = name(*a);
            *b = name(*b)
        }
        ok.sort_unstable();
        (self.sets.id(ok), arcs)
    }
    fn unclose(
        &mut self,
        st: usize,
        orig: usize,
        arcs: &[(u64, u64, Word, Word, usize)],
        block: usize,
        minimum: usize,
    ) -> (usize, Vec<Vec<HashSet<Word>>>) {
        let mut pred = HashMap::<u64, Vec<u64>>::new();
        for &(a, b, _, _, _) in arcs {
            pred.entry(b).or_default().push(a)
        }
        let mut seen = HashSet::new();
        let mut todo = vec![];
        for p in self.sets.items[st].clone() {
            let x = (self.sets.id(vec![p]) as u64) << 2;
            seen.insert(x);
            todo.push(x)
        }
        let mut i = 0;
        while i < todo.len() {
            let v = todo[i];
            i += 1;
            if let Some(ns) = pred.get(&v) {
                for &u in ns {
                    if seen.insert(u) {
                        todo.push(u)
                    }
                }
            }
        }
        let mut out = vec![];
        for p in self.sets.items[orig].clone() {
            if seen.contains(&(((self.sets.id(vec![p]) as u64) << 2) | (minimum > 0) as u64)) {
                out.push(p)
            }
        }
        let mut ok = vec![vec![HashSet::new(); self.h - 1]; block];
        for &(_, b, w, y, phase) in arcs {
            if seen.contains(&b) {
                for i in 0..self.h - 1 {
                    ok[phase][i].insert(pq(w, y, i, self.hor));
                }
            }
        }
        (self.sets.id(out), ok)
    }
    fn strip(
        &mut self,
        grid: &mut [usize],
        pos: usize,
        dom: &mut Dict<Vec<Word>>,
        gaps: &[usize],
        across: &[usize],
        period: usize,
        block: usize,
        minimum: usize,
        duplicate: bool,
    ) -> bool {
        let k = self.k;
        let h = self.h;
        let hor = self.hor;
        let stride=self.stride;
        let idx = |j, i| {
            let i = if duplicate { 0 } else { i };
            if hor {
                (pos + i) * stride + j
            } else {
                j * stride + pos + i
            }
        };
        let mut tt = vec![];
        for j in 0..k - 1 {
            tt.push(self.table((0..h - 1).map(|i| grid[idx(j, i)]).collect(), dom))
        }
        let mut fs = vec![];
        let mut start = vec![];
        for w in self.tabs[tt[0]].keys().copied().collect::<Vec<_>>() {
            let z = self.advance(0, w, self.stage(0));
            if z != BAD {
                start.push((w, z))
            }
        }
        start.sort_unstable();
        let mut st = self.sets.id(start);
        fs.push(st);
        let mut loops = HashMap::new();
        for (j, &t) in tt.iter().enumerate() {
            if gaps.contains(&j) {
                let old = st;
                let stage=self.stage(j+1);
                assert!((j..j+block).all(|v|self.stage(v+1)==stage));
                let (v, arcs) = self.close(st, &tt[j..j + block], period, minimum,stage);
                loops.insert(j, (old, arcs));
                st = v;
                fs[j] = st;
            }
            let end = j == k - 2;
            let stage = self.stage(j + 1);
            if let Some(v) = self.fwd.get(&(st, t, stage)) {
                st = *v
            } else {
                let mut nd = HashSet::new();
                for (w, z) in self.sets.items[st].clone() {
                    if let Some(ys) = self.tabs[t].get(&w).cloned() {
                        for y in ys {
                            let g = self.advance(z, y, stage);
                            if g != BAD {
                                let f = &self.forest.items[g as usize];
                                if !end || f.mark & !f.open == 0 {
                                    nd.insert((y, g));
                                }
                            }
                        }
                    }
                }
                let mut vv = nd.into_iter().collect::<Vec<_>>();
                vv.sort_unstable();
                let v = self.sets.id(vv);
                self.fwd.insert((st, t, stage), v);
                st = v;
            }
            fs.push(st);
            if self.sets.items[st].is_empty() {
                return false;
            }
        }
        let mut proj = vec![vec![]; k - 1];
        for j in (0..k - 1).rev() {
            let key = (fs[j], tt[j], st, self.stage(j + 1));
            if !self.back.contains_key(&key) {
                let mut prev = vec![];
                let mut ok = vec![HashSet::new(); h - 1];
                for (w, z) in self.sets.items[fs[j]].clone() {
                    let mut any = false;
                    if let Some(ys) = self.tabs[tt[j]].get(&w).cloned() {
                        for y in ys {
                            let g = self.advance(z, y, self.stage(j + 1));
                            if g != BAD && self.sets.items[st].binary_search(&(y, g)).is_ok() {
                                any = true;
                                for i in 0..h - 1 {
                                    ok[i].insert(pq(w, y, i, hor));
                                }
                            }
                        }
                    }
                    if any {
                        prev.push((w, z))
                    }
                }
                let ds = ok
                    .into_iter()
                    .map(|v| {
                        let mut a = v.into_iter().collect::<Vec<_>>();
                        a.sort_unstable();
                        dom.id(a)
                    })
                    .collect();
                let id = self.sets.id(prev);
                self.back.insert(key, (id, ds));
            }
            let (id, ds) = &self.back[&key];
            proj[j] = ds.clone();
            st = *id;
            if let Some((old, arcs)) = loops.get(&j) {
                let (before, ok) = self.unclose(st, *old, arcs, block, minimum);
                st = before;
                for (phase, sets) in ok.into_iter().enumerate() {
                    for (d, mut v) in proj[j + phase].iter_mut().zip(sets) {
                        v.extend(dom.items[*d].iter().copied());
                        let mut a = v.into_iter().collect::<Vec<_>>();
                        a.sort_unstable();
                        *d = dom.id(a)
                    }
                }
            }
        }
        for (j, ds) in proj.into_iter().enumerate() {
            if duplicate {
                let mut a = dom.items[ds[0]].clone();
                a.extend_from_slice(&dom.items[ds[1]]);
                a.sort_unstable();
                a.dedup();
                grid[idx(j, 0)] = dom.id(a);
                continue;
            }
            for i in 0..h - 1 {
                if h > 2
                    && across.iter().any(|&g| {
                        g <= pos + i && pos + i < g + block && (pos < g || pos + h - 2 >= g + block)
                    })
                {
                    continue;
                }
                grid[idx(j, i)] = ds[i]
            }
        }
        true
    }
    fn weighted_step(
        &mut self,
        st: &HashMap<(Word, u32), i32>,
        t: usize,
        stage: u8,
        end: bool,
    ) -> HashMap<(Word, u32), i32> {
        let mut nd = HashMap::new();
        for (&(w, z), &v) in st {
            if let Some(ys) = self.tabs[t].get(&w).cloned() {
                for y in ys {
                    let h = self.advance(z, y, stage);
                    if h == BAD {
                        continue;
                    }
                    let f = self.forest.items[h as usize];
                    if end && f.mark & !f.open != 0 {
                        continue;
                    }
                    let d = v + self.cost(y);
                    let b = nd.entry((y, h)).or_insert(d);
                    *b = (*b).min(d);
                }
            }
        }
        nd
    }
    fn cost(&self, w: Word) -> i32 {
        (0..self.h)
            .map(|i| {
                (1 + ((i == 0 && self.edge & 1 != 0) || (i + 1 == self.h && self.edge & 2 != 0))
                    as i32)
                    * (3 - slice(w, i).count_ones() as i32)
            })
            .sum()
    }
    fn price(&mut self, tt: &[usize], along: &[usize], block: usize, period: usize) -> i32 {
        let mut st = HashMap::new();
        for w in self.tabs[tt[0]].keys().copied().collect::<Vec<_>>() {
            let z = self.advance(0, w, self.stage(0));
            if z != BAD {
                st.insert((w, z), self.cost(w));
            }
        }
        for (j, &t) in tt.iter().enumerate() {
            if along.contains(&j) {
                let mut delta = st.clone();
                while !delta.is_empty() {
                    for i in 0..period {
                        delta = self.weighted_step(&delta, tt[j + i % block], 0, false)
                    }
                    delta.retain(|p, v| st.get(p).map_or(true, |a| *v < *a));
                    st.extend(delta.iter().map(|(&p, &v)| (p, v)));
                }
            }
            st = self.weighted_step(&st, t, self.stage(j + 1), j + 2 == self.k);
        }
        *st.values().min().expect("no strip at any price")
    }
}
fn strip_prices(
    k: usize,
    grid: &[usize],
    dom: &Dict<Vec<Word>>,
    gx: &[usize],
    gy: &[usize],
    block: usize,
    period: usize,
    q: Option<usize>,
) {
    for hor in [true, false] {
        let (along, across) = if hor { (gx, gy) } else { (gy, gx) };
        let mut memo = HashMap::new();
        let mut engines = HashMap::new();
        let mut bill = vec![0; 1 + across.len()];
        for i in 0..k - 1 {
            let edge = (i == 0) as u8 + 2 * ((i == k - 2) as u8);
            let omit = if let Some(p) = q {
                if hor && i == 0 {
                    2
                } else if !hor && i <= p && p < i + 2 {
                    1 << (3 * (p - i) + 1)
                } else {
                    0
                }
            } else {
                0
            };
            let ds = (0..k - 1)
                .map(|j| {
                    if hor {
                        grid[i * (k - 1) + j]
                    } else {
                        grid[j * (k - 1) + i]
                    }
                })
                .collect::<Vec<_>>();
            let key = (ds, edge, omit);
            if !memo.contains_key(&key) {
                let engine = engines
                    .entry((edge, omit))
                    .or_insert_with(|| Engine::new(k, 2, hor, edge, q, omit));
                let tt = key
                    .0
                    .iter()
                    .map(|&d| engine.table(vec![d], dom))
                    .collect::<Vec<_>>();
                memo.insert(key.clone(), engine.price(&tt, along, block, period));
            }
            let v = memo[&key];
            bill[0] += v;
            for (j, &g) in across.iter().enumerate() {
                if g <= i && i < g + block {
                    bill[1 + j] += v
                }
            }
        }
        println!("2D strip lower hor={hor} (base, added block copies) {bill:?}");
    }
}
fn main() {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    let hmax = args
        .iter()
        .filter_map(|v| v.parse::<usize>().ok())
        .next()
        .unwrap_or(3);
    let q = args
        .iter()
        .find_map(|v| v.strip_prefix("--exit="))
        .map(|v| v.parse::<usize>().unwrap());
    let gaps = |key: &str| {
        args.iter()
            .find_map(|v| v.strip_prefix(key))
            .map(|s| {
                s.split(',')
                    .map(|v| v.parse::<usize>().unwrap())
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default()
    };
    let (gx, gy) = (gaps("--gx="), gaps("--gy="));
    let period = args
        .iter()
        .find_map(|v| v.strip_prefix("--period="))
        .map(|s| s.parse().unwrap())
        .unwrap_or(1);
    let block = args
        .iter()
        .find_map(|v| v.strip_prefix("--block="))
        .map(|s| s.parse().unwrap())
        .unwrap_or(1);
    let positive = args.iter().any(|s| s == "--positive");
    let minimum = args
        .iter()
        .find_map(|v| v.strip_prefix("--min-copies="))
        .map(|s| s.parse().unwrap())
        .unwrap_or(0);
    assert!(block > 0 && period > 0 && period % block == 0 && (!positive || block == 1));
    let rounds = args
        .iter()
        .find_map(|v| v.strip_prefix("--rounds="))
        .map(|s| s.parse().unwrap())
        .unwrap_or(1);
    let passes = args
        .iter()
        .find_map(|v| v.strip_prefix("--passes="))
        .map(|s| s.parse().unwrap())
        .unwrap_or(40);
    assert!((2..=4).contains(&hmax));
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input
        .split_ascii_whitespace()
        .map(|s| s.parse::<usize>().unwrap());
    let k = it.next().unwrap();
    let height=args.iter().find_map(|v|v.strip_prefix("--height=")).map(|s|s.parse().unwrap()).unwrap_or(k);
    let root=args.iter().find_map(|v|v.strip_prefix("--root-from=")).map(|s|s.parse::<usize>().unwrap());
    let low=root.is_some();let high=args.iter().any(|s|s=="--open-south");
    let sides=args.iter().find_map(|v|v.strip_prefix("--sides=")).map(|s|s.parse::<u8>().unwrap()).unwrap_or(3);
    let sealed=args.iter().any(|s|s=="--sealed-north");
    let n = it.next().unwrap();
    let mut dom = Dict::new();
    let mut index = vec![];
    for _ in 0..n {
        let mut a = vec![];
        for _ in 0..it.next().unwrap() {
            let mut p = 0;
            for i in 0..4 {
                p |= (it.next().unwrap() as u64) << (9 * i)
            }
            a.push(p)
        }
        a.sort_unstable();
        index.push(dom.id(a))
    }
    let mut grid = it.map(|n| index[n]).collect::<Vec<_>>();
    assert_eq!(grid.len(), (k - 1) * (height - 1));
    for _ in 0..rounds {
        let orig = grid.clone();
        for h in 2..=hmax {
            for pass in 0..passes {
                let old = grid.clone();
                for hor in [true, false] {
                    let mut engines = HashMap::new();
                    let (along, across) = if hor { (&gx, &gy) } else { (&gy, &gx) };
                    let wide=if hor{height}else{k};let length=if hor{k}else{height};
                    let mut starts: Vec<_> = (0..=wide - h)
                        .map(|j| (if pass % 2 == 0 { j } else { wide - h - j }, false))
                        .collect();
                    if positive && h == 3 {
                        starts.extend(across.iter().map(|&g| (g, true)))
                    }
                    for (x, duplicate) in starts {
                        if h > 3
                            && across.iter().any(|&g| {
                                x < g + block
                                    && x + h - 2 >= g
                                    && !(x >= g && x + h - 2 < g + block)
                            })
                        {
                            continue;
                        }
                        let edge = ((x == 0 && !(hor && low)) as u8 + 2 * ((x + h == wide && !(hor && high)) as u8)) & if hor{3}else{sides};
                        let omit = match q {
                            Some(_) if hor && x == 0 => 2,
                            Some(p) if !hor && x <= p && p < x + h => 1 << (3 * (p - x) + 1),
                            _ => 0,
                        };
                        let trunk=if hor{0}else{(0..h).filter(|&i|root.map_or(false,|f|x+i>=f)).map(|i|1<<(3*i)).sum()};
                        let rf=if hor && x==0{root}else{None};
                        let make=||{let mut e=Engine::new(length,h,hor,edge,q,omit);
                            e.stride=k-1;e.open_north=if hor{sides&1==0}else{low};e.open_south=if hor{sides&2==0}else{high};e.sealed=!hor && sealed;e.trunk=trunk;e.rootfrom=rf;e};
                        let engine=engines.entry((edge,omit,trunk,rf)).or_insert_with(make);
                        if !engine.strip(
                            &mut grid, x, &mut dom, along, across, period, block, minimum,
                            duplicate,
                        ) {
                            println!("EMPTY h={h} pass={pass} horizontal={hor} start={x}");
                            return;
                        }
                        // Bound resident cache size. Eviction changes no allowed state.
                        if engine.back.len() > 9000
                            || engine
                                .sets
                                .items
                                .iter()
                                .rev()
                                .take(30)
                                .any(|v| v.len() > 20000)
                        {
                            *engine = make();
                        }
                    }
                }
                let diff = grid.iter().zip(old).filter(|(a, b)| **a != *b).count();
                println!(
                    "h={h} pass={pass} changed={diff} local_domains={}",
                    dom.items.len()
                );
                if diff == 0 {
                    break;
                }
            }
        }
        if orig == grid {
            if args.iter().any(|x|x=="--emit"){
                let mut seen=HashMap::new();
                println!("DOMAINS");
                for d in &grid{if !seen.contains_key(d){
                    seen.insert(*d,seen.len());
                    for v in &dom.items[*d]{print!("{v} ")}println!()
                }}
                println!("GRID");
                for d in &grid{print!("{} ",seen[d])}println!()
            }
            if args.iter().any(|x| x == "--account") {
                account(k, &grid, &dom, &gx, &gy, block)
            }
            if args.iter().any(|x| x == "--price") {
                strip_prices(k, &grid, &dom, &gx, &gy, block, period, q)
            }
            println!("OPEN (joint strip fixed point)");
            return;
        }
    }
    println!("OPEN (strip consistency only)")
}
