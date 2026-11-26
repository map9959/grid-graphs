//! Exact induced forest on a free-ended bent strip, incl. the inner tip square.
use std::collections::HashMap;
use std::io::{self,Read};
type Pt=(i32,i32);
fn neighbours((y,x):Pt)->[Pt;4]{[(y-1,x),(y+1,x),(y,x-1),(y,x+1)]}
fn rt(p:&[usize;16],mut x:usize)->usize{while p[x]!=x{x=p[x]}x}
fn solve(order:&[(Pt,u8)],trace:bool,contacts:&HashMap<Pt,bool>)->(i32,Vec<Pt>){
    let wired=!contacts.is_empty();
    let mut buf=vec![];if wired{buf.push(((-999,-999),1));buf.extend_from_slice(order);}
    let order=if wired{buf.as_slice()}else{order};
    let id:HashMap<_,_>=order.iter().enumerate().map(|(i,&(p,_))|(p,i)).collect();
    let mut last:Vec<_>=order.iter().enumerate().map(|(i,(p,_))|neighbours(*p).iter().filter_map(|q|id.get(q)).copied().max().unwrap_or(i).max(i)).collect();
    if wired{last[0]=order.len()-1;}
    let mut live=Vec::new();let mut layers=Vec::new();
    for (i,&(p,_)) in order.iter().enumerate(){
        let len=live.len();assert!(len<=12);
        let prev:Vec<_>=neighbours(p).iter().filter_map(|q|id.get(q)).filter(|&&j|j<i).map(|j|live.iter().position(|k|k==j).unwrap()).collect();
        live.push(i);let kept:Vec<_>=(0..live.len()).filter(|&v|last[live[v]]>i).collect();
        assert!(kept.len()<=12);live=kept.iter().map(|&v|live[v]).collect();layers.push((len,prev,kept));
    }
    let advance=|i:usize,d:&HashMap<u64,i32>,trace:bool|{
        let(p,allowed)=order[i];let(len,prev,kept)=&layers[i];let len=*len;
        let mut nd=HashMap::new();let mut pred=HashMap::new();
        for (&s,&z) in d{
            for m in 0..=1{
                if allowed&(1<<m)==0{continue}
                let mut par=std::array::from_fn(|j|if j<len{((s>>(5*j))&15) as usize}else{j});let mut ok=true;
                for &v in prev{if m!=0||s&(16<<(5*v))!=0{
                    let a=rt(&par,v);let b=rt(&par,len);if a==b{ok=false;break}par[a]=b;
                }}
                if !ok{continue}
                if let Some(&back)=contacts.get(&p){if m!=0||back{
                    let a=rt(&par,0);let b=rt(&par,len);if a==b{continue}par[a]=b;
                }}
                let mut first=[16usize;16];let mut k=0;
                for (j,&v) in kept.iter().enumerate(){
                    let r=rt(&par,v);if first[r]==16{first[r]=j}
                    let b=if v==len{m as u64*16}else{(s>>(5*v))&16};k|=(first[r] as u64|b)<<(5*j);
                }
                let e=nd.entry(k).or_insert(i32::MIN);let cost=z+m as i32;
                let path=(s<<1)|m as u64;
                if cost>*e{*e=cost;if trace{pred.insert(k,path);}}
                else if trace&&cost==*e{let p=pred.get_mut(&k).unwrap();*p=(*p).min(path);}
            }
        }
        (nd,pred)
    };
    let mut d=HashMap::from([(0u64,0)]);let mut checkpoints=vec![];
    for i in 0..order.len(){
        if trace&&i%32==0{checkpoints.push((i,d.clone()));}d=advance(i,&d,false).0;
    }
    let mut marks=vec![];let mut s=0;
    for (lo,mut f) in checkpoints.into_iter().rev(){
        let mut history=vec![];
        for i in lo..order.len().min(lo+32){let(g,p)=advance(i,&f,true);f=g;history.push((i,p));}
        for (i,pred) in history.into_iter().rev(){
            let step=pred[&s];if step&1!=0{marks.push(order[i].0)}s=step>>1;
        }
    }
    (d[&0],marks)
}
fn elbow(w:i32,h:i32,v:i32)->Vec<(Pt,u8)>{
    let mut a=Vec::new();
    for x in (w..w+h).rev(){for y in 0..w{a.push(((y,x),3))}}
    for t in (1-w..w).rev(){
        for y in 0..w{let x=y+t;if x>=0&&x<w{a.push(((y,x),3));}}
        if t==0{a.push(((w,w),1));}
    }
    for y in w..w+v{for x in 0..w{a.push(((y,x),3))}}
    a
}
fn flagged(order:&[(Pt,u8)],terms:&[Pt],ports:&HashMap<Pt,(usize,usize)>,scale:i32,price:Option<i32>)->HashMap<u128,i32>{
    let id:HashMap<_,_>=order.iter().enumerate().map(|(j,&(p,_))|(p,j)).collect();
    let last:Vec<_>=order.iter().enumerate().map(|(i,(p,_))|neighbours(*p).iter().filter_map(|q|id.get(q)).copied().max().unwrap_or(i).max(i)).collect();
    let mut live=vec![];let mut d=HashMap::from([(0u128,0)]);
    for (i,&(p,allowed)) in order.iter().enumerate(){
        let l=live.len();let prev:Vec<_>=neighbours(p).iter().filter_map(|q|id.get(q)).filter(|&&j|j<i).map(|j|live.iter().position(|k|k==j).unwrap()).collect();
        live.push(i);let kept:Vec<_>=(0..live.len()).filter(|&j|last[live[j]]>i).collect();
        let mut e=HashMap::new();
        for (&s,&z) in &d{for m in 0..2{if allowed&(1<<m)==0{continue}
            let mut q=std::array::from_fn(|j|if j<l{((s>>(6*j))&15)as usize}else{j});
            let mut flags:[bool;16]=std::array::from_fn(|j|j<l&&s&(32<<(6*j))!=0);
            let (must,opt)=ports.get(&p).copied().unwrap_or((0,0));
            let hits=must+if m>0{opt}else{0}+usize::from(terms.contains(&p));
            flags[l]=hits>0;
            let mut rank=(s>>96)+hits.saturating_sub(1) as u128;let mut ok=true;
            for &v in &prev{if m!=0||s&(16<<(6*v))!=0{
                let a=rt(&q,v);let b=rt(&q,l);if a==b{ok=false;break}
                rank+=(flags[a]&&flags[b])as u128;flags[b]|=flags[a];q[a]=b;
            }}
            if !ok{continue}
            let mut ids=[16;16];let mut key=if price.is_none(){rank<<96}else{0};
            for (j,&v) in kept.iter().enumerate(){
                let r=rt(&q,v);ids[r]=ids[r].min(j);
                let mark=if v==l{m as u128*16}else{(s>>(6*v))&16};
                key|=(mark|ids[r]as u128|32*flags[r]as u128)<<(6*j);
            }
            let entry=e.entry(key).or_insert(i32::MIN);*entry=(*entry).max(z+scale*m-price.unwrap_or(0)*rank as i32);
        }}
        live=kept.iter().map(|&v|live[v]).collect();d=e;
    }
    d
}
fn dense_ranks(h:i32,v:i32,left:u8,right:u8){
    assert!(h>=0&&v>=0);
    let mut order=elbow(9,2+h,2+v);let mut terms=vec![];
    for &mut ((y,x),ref mut f) in &mut order{
        if x==10+h||y==10+v{
            let depth=x.min(y);
            let mask=if x==10+h{left}else{right};
            let bit=if depth<8{mask>>(7-depth)&1}else{0};*f=1<<bit;
            if bit!=0{terms.push((y,x));}
        }else if x>=10&&y==8||y>=10&&x==8{*f=1}
    }
    let d=flagged(&order,&terms,&HashMap::new(),1,None);
    let prices=(0..6).map(|i|d.get(&(i<<96)).unwrap_or(&-99)-6).collect::<Vec<_>>();
    if h<=3&&v<=3&&left==146&&right==146{assert_eq!(prices,[36,36,37,38,38,39].map(|x|x+3*(h+v)));}
    println!("shift ({h},{v}), corner scores excluding the end masks, by port rank: {prices:?}");
}
fn main(){
    let a:Vec<_>=std::env::args().skip(1).collect();
    let num=|i:usize|a[i].parse::<i32>().unwrap();
    if a[0]=="dense-ranks"{
        let mask=|i|a.get(i).map(|s:&String|s.parse::<u8>().unwrap()).unwrap_or(146);
        dense_ranks(a.get(1).map_or(0,|_|num(1)),a.get(2).map_or(0,|_|num(2)),mask(3),mask(4));return
    }
    if a[0]=="critical-corner"||a[0]=="critical-ranks"{
        let (a,b)=(num(1),num(2));let mut mx=i32::MIN;
        let ranked=std::env::args().nth(1).as_deref()==Some("critical-ranks");
        let bars=|m:i32|match m{509=>1,489=>9,329=>73,_=>m};
        let mut v=[-999;6];
        for inner in 0..=1{
            let mut o=elbow(9,2,2);
            for ((y,x),f) in &mut o{if *x==10{*f=1<<((a>>*y)&1)}else if *y==10{*f=1<<((b>>*x)&1)}
                else if (*y,*x)==(9,9){*f=1<<inner}
                else if a==329&&(*y,*x)==(8,9)&&std::env::var_os("BLOCK_X").is_some()
                    ||b==329&&(*y,*x)==(9,8)&&std::env::var_os("BLOCK_Y").is_some(){*f=2}}
            if ranked{
                let terms:Vec<_>=o.iter().map(|(p,_)|*p).filter(|&(y,x)|x==10&&bars(a)>>y&1!=0||y==10&&bars(b)>>x&1!=0).collect();
                let t=flagged(&o,&terms,&HashMap::new(),3,None);
                for (j,z) in v.iter_mut().enumerate(){if let Some(&p)=t.get(&((j as u128)<<96)){
                    *z=(*z).max(p-3*(a.count_ones()+b.count_ones())as i32-inner);
                }}
            }else{
                let(z,_)=solve(&o,false,&HashMap::new());
                mx=mx.max(3*(z-a.count_ones()as i32-b.count_ones()as i32)-inner);
            }
        }
        if ranked{println!("{v:?}")}else{println!("{mx}")}return
    }
    if a[0]=="nine-bases"{
        let mut cap=i32::MIN;
        for h in 16..20{for v in 16..20{
            cap=cap.max(2*solve(&elbow(9,h,v),false,&HashMap::new()).0-7*(h+v));
        }}
        assert_eq!(cap,67);println!("16 free corner bases: 2*marks-7*(h+v) <= {cap}");return
    }
    if a[0]=="dense-corner"{
        let mut order=elbow(10,1,1);
        for &mut ((y,x),ref mut flag) in &mut order{
            if x==10||y==10{
                let j=x.min(y);*flag=if j==0||j==3||j==6{2}else{1}
            }
            if x==9&&y==9{*flag=1;}
        }
        println!("{}",solve(&order,false,&HashMap::new()).0-6);return
    }
    if a[0]=="bases"{
        for (h,v,z) in [(13,13,143),(0,13,94),(13,0,94)]{
            assert_eq!(solve(&elbow(10,h,v),false,&HashMap::new()).0,z);
            println!("10-layer elbow({h},{v}) = {z}");
        }return
    }
    if a[0]=="elbow"||a[0]=="witness"{
        let (z,m)=solve(&elbow(num(1),num(2),num(3)),a[0]=="witness",&HashMap::new());
        println!("{z}");for (y,x) in m{println!("{y} {x}");}return
    }
    assert!(a[0]=="outer"||a[0]=="inner"||a[0]=="repair"||a[0]=="port-cap"||a[0]=="port-price"||a[0]=="bridge-price"||a[0]=="closed-price");
    let w=num(1);let fixed=num(2);let mut input=String::new();io::stdin().read_to_string(&mut input).unwrap();
    let rows:Vec<_>=input.split_whitespace().map(|s|s.as_bytes()).collect();let n=rows[0].len() as i32;
    let select=a[0]=="port-cap";let priced=a[0]=="port-price";
    let pc=select||priced;assert_eq!(rows.len(),n as usize*(if select{5}else{1}));
    let mut parts=vec![];
    let mut witness=vec![];
    if a[0]=="closed-price"{
        assert!(w<=5);
        let mut sweep=vec![];let mut ps=HashMap::new();
        for s in 0..4{
            for ((mut y,mut x),mut f) in elbow(w,n/2-w,n-n/2-w){
                for _ in 0..s{(y,x)=(n-1-x,y)}
                if f!=1{
                    let b=rows[y as usize][x as usize]-b'A';
                    if b>=9{f=1;}
                    ps.insert((y,x),((b%9/3)as usize,(b%3)as usize));
                }
                sweep.push(((y,x),f));
            }
        }
        println!("[{}]",flagged(&sweep,&[],&ps,num(3),Some(num(4)))[&0]);return
    }
    for side in 0..4{
        let mut order=elbow(w,n/2-w,n-n/2-w);let mut subtract=0;
        let rot=|mut i:i32,mut j:i32|{for _ in 0..side{(i,j)=(j,n-1-i)}(i,j)};
        if a[0]=="bridge-price"{
            let mut ps=HashMap::new();order.retain(|&(p,_)|p!=(w,w));
            for (p,f) in &mut order{let(i,j)=rot(p.0,p.1);
                let b=rows[i as usize][j as usize]-b'A';
                if b>=9{*f=1;}
                ps.insert(*p,((b%9/3)as usize,(b%3)as usize));
            }
            parts.push(flagged(&order,&[],&ps,num(3),Some(num(4)))[&0]);continue
        }
        let repair=a[0]=="repair";let mut contacts=HashMap::new();
        if repair||pc{
            order.retain(|&(p,_)|p!=(w,w)); // the inner corner is part of the core
        }
        for ((y,x),flag) in &mut order{
            if *flag==1{continue}
            let depth=(*y).min(*x);
            if repair{
                // End each arm one column early. Its blank last slice
                // carries the possible indirect contact into a core mark.
                if *x==n/2-1||*y==n-n/2-1{*flag=1;}
                if depth==w-1&&(*x).max(*y)>=w{
                    let (i,j)=rot((*y).max(w),(*x).max(w));
                    contacts.insert((*y,*x),rows[i as usize][j as usize]==b'#');
                }
            }
            if pc&&depth==w-1&&(*x).max(*y)>=w{
                let (i,j)=rot((*y).max(w),(*x).max(w));
                if priced||rows[(n*(side+1)+i)as usize][j as usize]==b'#'{
                    contacts.insert((*y,*x),rows[i as usize][j as usize]==b'#');
                }
            }
            if pc{
                let(i,j)=rot(*y,*x);
                for u in [i-1,i+1]{for v in [j-1,j+1]{
                    if u>=w&&v>=w&&u<n-w&&v<n-w&&rows[u as usize][v as usize]==b'#'{*flag=1;}
                }}
            }
            if ((a[0]=="outer"||pc)&&depth<fixed)||(a[0]=="inner"&&depth>=fixed){
                let(i,j)=rot(*y,*x);
                let m=rows[i as usize][j as usize]==b'#';assert!(!m||*flag&2!=0);*flag=if m{2}else{1};
                if a[0]=="inner"&&m{subtract+=1;}
            }
        }
        let(z,m)=if priced{
            let ps=contacts.iter().map(|(&k,&b)|(k,(b as usize,!b as usize))).collect();
            (flagged(&order,&[],&ps,num(3),Some(num(4)))[&0],vec![])
        }else{solve(&order,repair,&contacts)};parts.push(z-subtract);
        witness.extend(m.into_iter().map(|(y,x)|rot(y,x)));
    }
    println!("{parts:?}");
    for (y,x) in witness{println!("{y} {x}");}
}
