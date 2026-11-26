//! Max-plus closure of a nine-layer corner with two variable-length arms.
//! Straight arms include the physical depth-nine path, holes and all.
use std::collections::HashMap;
type Pt=(i16,i16);
#[derive(Clone,Copy)]
struct V{z:i32,tags:u64}
type Table=HashMap<u128,V>;
fn improve(t:&mut Table,k:u128,v:V)->bool{
    let old=t.entry(k).or_insert(V{z:i32::MIN,tags:0});
    if v.z>old.z{*old=v;true}
    else if v.z==old.z&&v.tags&!old.tags!=0{old.tags|=v.tags;true}else{false}
}
const AGE:u32=100;
static BAN:std::sync::OnceLock<u8>=std::sync::OnceLock::new();
static OPEN8:std::sync::OnceLock<bool>=std::sync::OnceLock::new();
static STRIDE:std::sync::OnceLock<u8>=std::sync::OnceLock::new();
static EXACT:std::sync::OnceLock<bool>=std::sync::OnceLock::new();
static SPARSE:std::sync::OnceLock<bool>=std::sync::OnceLock::new();
static FILTER:std::sync::OnceLock<[[u64;2];10]>=std::sync::OnceLock::new();
static FEES:std::sync::OnceLock<Option<[i32;2]>>=std::sync::OnceLock::new();
struct Site{n:usize,prev:Vec<usize>,seam:Option<usize>,keep:Vec<usize>,p:Pt}
fn root(q:&[usize;16],mut i:usize)->usize{while i!=q[i]{i=q[i]}i}
fn geometry()->Vec<Site>{
    let mut pts=vec![];
    for x in (9..=11).rev(){for y in 0..if x>=10{10}else{9}{pts.push((y,x))}}
    for t in (-8..=8).rev(){
        for y in 0..9{let x=y+t;if (0..9).contains(&x){pts.push((y,x))}}
        if t==0{pts.push((9,9))}
    }
    for y in 9..=11{for x in 0..if y>=10{10}else{9}{pts.push((y,x))}}
    let id:HashMap<_,_>=pts.iter().enumerate().map(|(i,&p)|(p,i)).collect();
    let adj=|&(y,x):&Pt|[(y+1,x),(y-1,x),(y,x+1),(y,x-1)];
    let last:Vec<_>=pts.iter().map(|p|adj(p).iter().filter_map(|t|id.get(t)).copied().max().unwrap()).collect();
    let mut live:Vec<usize>=vec![];
    pts.iter().enumerate().map(|(i,&p)|{
        let n=live.len();assert!(n<16);
        let prev=adj(&p).iter().filter_map(|v|id.get(v)).filter_map(|j|live.iter().position(|k|k==j)).collect();
        let seam=if p.1==11{(p.0-1,p.1)}else{(p.0,p.1-1)};
        let seam=id.get(&seam).and_then(|v|live.iter().position(|j|j==v));
        live.push(i);let mut keep:Vec<_>=(0..=n).filter(|&v|last[live[v]]>i).collect();
        keep.sort_by_key(|&j|pts[live[j]]);
        live=keep.iter().map(|&v|live[v]).collect();
        Site{p,n,prev,seam,keep}
    }).collect()
}
fn run(d:Table,sites:&[Site],gap:u8,word:u8,wild:bool)->Table{pinned(d,sites,gap,word,wild,&[])}
fn pinned(mut d:Table,sites:&[Site],gap:u8,word:u8,wild:bool,pins:&[u8])->Table{
    if sites[0].p==(0,9){
        // The two depth-nine bar ends adjoining a reentrant corner are
        // diagonal in the physical grid. The fourth unit-square site is
        // inside the retained core. Remember the incoming end through
        // the bend; the first outgoing back bit completes this test.
        assert_eq!(sites[0].n,10);
        d=d.into_iter().map(|(s,v)|{assert_eq!(s>>127,0);(s|(((s>>(6*9+4))&1)<<127),v)}).collect()
    }
    for (i,site) in sites.iter().enumerate(){
        let Site{n,prev,keep,seam,p:(y,x)}=site;let n=*n;
        let (a,t)=((*y).max(*x),(*y).min(*x));
        let end=a==11;let back=a>=10&&t==9;
        let cutbit=end&&t<8&&(word>>(7-t)&1)!=0;
        let fixed=if word==254&&!end&&a>=10&&[0,1,3,4,6,7].contains(&t){Some((t==0)as usize)}
            else if end&&!back&&(!wild||word!=255){Some(cutbit as usize)}else if a>=10&&t==8&&!*OPEN8.get().unwrap()||(*y,*x)==(9,9){Some(0)}else{None};
        let mut e=Table::new();
        for (&s,&z) in &d{for m in 0..2usize{
            if !pins.is_empty()&&pins[i]as usize!=m{continue}
            if fixed.is_some_and(|b|m!=b){continue}
            let mut age=(s>>AGE)as u8;
            let exact=*EXACT.get().unwrap();let mut rank=(s>>116)as u8;
            let mut candidates=if a>=10&&t==0{*BAN.get().unwrap()}else{(s>>108)as u8};
            if candidates!=0&&t<8{
                for (i,mask) in [146u8,145,137,73].iter().enumerate(){
                    if (mask>>(7-t)&1)as usize!=m{candidates &= !(1<<i)}
                }
            }
            if t==8{if m==0&&candidates!=0{continue}candidates=0}
            let mut defect=0;
            if back{
                if m==0&&age<gap-1{
                    if let Some(f)=FEES.get().unwrap(){defect=f[age as usize]}else{continue}
                }
                age=if m==0{0}else{(age+1).min(gap-1)};
            }
            if a<10{age=gap-1}
            let mut q=std::array::from_fn(|i|if i<n{(s>>(6*i)&15)as usize}else{i});
            let mut f:[bool;16]=std::array::from_fn(|i|i<n&&s&(32<<(6*i))!=0);
            let sparse=*SPARSE.get().unwrap();
            f[n]=if sparse{end&&(back||m!=0)}else{cutbit||end&&wild};
            let mut score=z.z-defect+if back{0}else if wild&&!end{6*m as i32}else{3*m as i32};
            let mut corner=s>>127;
            if back&&*y>=10{if corner!=0&&m!=0{continue}corner=0}
            let mut history=0;
            if sparse&&end{
                let hist=if t==0{0}else{(s>>124)as usize&3};
                if !back{score+=2*m as i32;if m!=0&&hist!=0{score+=2}}
                else if hist&1!=0||hist&2!=0&&m!=0{score+=2}
                if !back{history=((hist<<1)|m)&3}
            }else if end&&wild&&seam.is_some_and(|j|m!=0||s&(16<<(6*j))!=0){score+=2}
            let mut ok=true;
            for &j in prev{if m!=0||s&(16<<(6*j))!=0{
                let u=root(&q,j);let v=root(&q,n);if u==v{ok=false;break}
                if f[u]&&f[v]{if exact{rank+=1}else{score-=if wild{4}else{2}}}f[v]|=f[u];q[u]=v;
            }}
            if !ok||exact&&rank>2{continue}
            let mut k=((age as u128)<<AGE)|((candidates as u128)<<108)|((rank as u128)<<116)|((history as u128)<<124)|(corner<<127);let mut ids=[16;16];
            for (j,&v) in keep.iter().enumerate(){
                let r=root(&q,v);ids[r]=ids[r].min(j);
                let b=if v==n{m as u128*16}else{s>>(6*v)&16};
                k|=(ids[r]as u128|b|32*f[r] as u128)<<(6*j)
            }
            improve(&mut e,k,V{z:score,tags:if end{z.tags&FILTER.get().unwrap()[t as usize][m]}else{z.tags}});
        }}
        d=e
    }d
}
fn replay(input:&str,g:&[Site],gap:u8,offset:u8,sparse:bool){
    let rows:Vec<_>=input.split_whitespace().map(str::as_bytes).collect();
    let n=rows.len()as i16;assert!(rows.iter().all(|s|s.len()==n as usize));
    let m=n-20;let cut=10+offset as i16;let l=g.len();
    let mut d=Table::from([(((gap-1)as u128)<<AGE,V{z:0,tags:u64::MAX})]);
    let mut push=|sites:&[Site],side:u8,dir:u8,shift:i16|{
        let pins:Vec<_>=sites.iter().map(|s|{
            let (mut y,mut x)=s.p;if (y,x)==(9,9){return 0}
            if dir==1{x+=shift}if dir==2{y+=shift}
            for _ in 0..side{(y,x)=(n-1-x,y)}
            (rows[y as usize][x as usize]==b'#')as u8
        }).collect();
        d=pinned(std::mem::take(&mut d),sites,gap,255,true,&pins);
        assert_eq!(d.len(),1,"physical slice rejected");
    };
    push(&g[..10],0,1,cut-11);
    for x in (10..cut).rev(){push(&g[10..20],0,1,x-10)}
    for side in 0..4{push(&g[20..l-20],side,0,0);
        for y in 10..if side==3{n-1-cut}else{n-10}{push(&g[l-20..l-10],side,2,y-10)}
    }
    push(&g[l-10..],3,2,n-1-cut-11);
    let scalar=d.values().next().unwrap().z-18*(4*m as i32-1);
    let t:i32=rows.iter().enumerate().map(|(i,s)|s.iter().enumerate().filter(|&(j,&v)|v==b'#'&&i.min(j).min(n as usize-1-i).min(n as usize-1-j)<9).count()as i32).sum();
    let delta=6*(t-12*m as i32);let slack=scalar+if sparse{-18}else{18};
    assert!(slack>=delta&&(slack-delta)%4==0);
    println!("physical outer nine {t}, normalized scalar {scalar}, independent seam rank allowance left {}",(slack-delta)/4);
}
fn closure(mut d:Table,col:&[Site],gap:u8,wild:bool)->Table{
    assert!(col.len()==10&&col[0].n==10&&col[9].keep.len()==10);
    for h in 1..=200{
        let stride=*STRIDE.get().unwrap();
        let mut f=d.clone();for _ in 0..stride{f=run(f,col,gap,0,wild)}
        let mut change=false;
        for (k,mut v) in f{v.z-=stride as i32*if wild{18}else{9};change|=improve(&mut d,k,v)}
        if !change{println!("prefix lengths through {} dominate all lengths, {} states",h-1,d.len());return d}
    }panic!("no postfixed envelope")
}
fn main(){
    let args:Vec<u8>=std::env::args().skip(1).map(|s|s.parse().unwrap()).collect();
    let gap=args[0];let a=args[1];let b=args[2];let wild=args.get(5)==Some(&1);
    BAN.set(args.get(6).copied().unwrap_or(0)).unwrap();
    OPEN8.set(args.get(7)==Some(&1)).unwrap();
    let offset=args.get(8).copied().unwrap_or(0);
    let stride=args.get(9).copied().unwrap_or(1);
    assert!(stride==1||wild&&stride==3);STRIDE.set(stride).unwrap();
    let exact=args.get(10)==Some(&1);assert!(!exact||!wild&&a==b&&args[3]==4);EXACT.set(exact).unwrap();
    let sparse=args.get(11)==Some(&1);assert!(!sparse||wild);SPARSE.set(sparse).unwrap();
    FEES.set(std::env::var("DENSE_DEFECT_FEES").ok().map(|s|{assert_eq!(gap,3);
        let (x,y)=s.split_once(',').unwrap();[x.parse().unwrap(),y.parse().unwrap()]})).unwrap();
    let lock=std::env::var_os("DENSE_TAG_LOCK").is_some();
    let bits=&args[12.min(args.len())..];assert!(bits.len()<=6);
    let mut f=[[u64::MAX;2];10];
    for (i,&t) in bits.iter().enumerate(){f[t as usize]=[0;2];for j in 0..64{f[t as usize][j>>i&1]|=1<<j}}
    FILTER.set(f).unwrap();
    assert!(gap>=3&&(wild||[146,145,137,73].contains(&a)&&[146,145,137,73].contains(&b)));
    let g=geometry();let l=g.len();
    if std::env::var_os("DENSE_REPLAY").is_some(){
        use std::io::Read;let mut text=String::new();std::io::stdin().read_to_string(&mut text).unwrap();
        assert!(wild);replay(&text,&g,gap,offset,sparse);return
    }
    let d=run(HashMap::from([(((gap-1)as u128)<<AGE,V{z:0,tags:u64::MAX})]),&g[..10],gap,a,wild);
    let mut d=if wild{d}else{closure(d,&g[10..20],gap,wild)};
    let corners=args.get(3).copied().unwrap_or(1);
    let min=args.get(4).copied().unwrap_or(1);
    if stride==3{assert!(min%3==2)}
    if wild{assert!(min>offset);for _ in 0..offset{d=run(d,&g[10..20],gap,0,wild);
        for v in d.values_mut(){v.z-=18}}}
    for _ in 1..corners{
        d=run(d,&g[20..l-20],gap,0,wild);
        if lock{assert!(wild&&min>=8&&gap==3&&sparse)}
        for j in 0..min{
            if lock&&j==4{d=closure(d,&g[l-20..l-10],gap,wild);}
            let word=if lock&&(j==3||j==min-4){254}else{0};
            d=run(d,&g[l-20..l-10],gap,word,wild);
            for v in d.values_mut(){v.z-=if wild{18}else{9}}
        }
        if !lock{d=closure(d,&g[l-20..l-10],gap,wild);}
    }
    let mut d=run(d,&g[20..l-20],gap,0,wild);
    if wild{for _ in 1..min-offset{d=run(d,&g[l-20..l-10],gap,0,wild);
        for v in d.values_mut(){v.z-=18}}}
    let d=closure(d,&g[l-20..l-10],gap,wild);
    let d=run(d,&g[l-10..],gap,b,wild);
    let best=d.values().map(|v|v.z).max().unwrap();
    let tags=d.values().filter(|v|v.z==best).fold(0,|s,v|s|v.tags);
    if wild{assert_eq!(corners,4);let s=best-i32::from(tags==0);
        println!("arbitrary seam: scalar {best}, matching maximizer tags {tags:#x}, 9-layer overhead <= {}",(s+if sparse{-18}else{18})/6);return}
    let cap=best-i32::from(tags==0)-18;
    if exact{println!("physical rank <=2: 9-layer overhead <= {}",cap/3);return}
    println!("cuts {a},{b} gap {gap}, {corners} corners: 3*marks(excluding ends)-9*free_slices-2*rank <= {cap}");
}
