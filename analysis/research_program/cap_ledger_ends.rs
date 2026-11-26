//! Rooted top/bottom end prices for telescoping an arbitrary-height cap.
use std::collections::HashMap;
type S=(i32,u64,u16,u8);
fn rt(p:&[usize;20],mut i:usize)->usize{while p[i]!=i{i=p[i]}i}
fn main(){
    let a:Vec<i32>=std::env::args().skip(1).map(|s|s.parse().unwrap()).collect();
    let (w,top,q,al,l,gc)=(a[0]as usize,a[1]==1,a[2],a[3],a[4],a[5]);
    assert!(w>0&&w<=9&&q%3==0);
    let back=1<<(w-1);let all=2*back-1;
    let init:S=(-1,(0..=w).map(|i|(i as u64)<<(4*i)).sum(),0,0);
    let mut st=vec![init];let mut ix=HashMap::from([(init,0u32)]);let mut arcs=vec![];let mut starts=vec![];let mut i=0;
    while i<st.len(){starts.push(arcs.len());let(old,part,flags,phase)=st[i];
        let mut free=if old<0{all}else{all&!(old<<1|old>>1)};
        if !top||phase!=0{free&=!1}
        let mut m=free;loop{
            let mut p=std::array::from_fn(|j|if j<w{(part>>(4*j)&15)as usize}else{j});
            let xr=(part>>(4*w)&15)as usize;if xr<w{p[2*w]=xr}
            let mut f:[bool;20]=std::array::from_fn(|j|j<w&&flags>>j&1!=0);
            f[2*w]=flags>>w&1!=0;f[2*w-1]=true;
            let cnt=if top{(m&(back-1)).count_ones()as i32}else{m.count_ones()as i32+1};
            let len=if top{w as i32-1}else{w as i32+1};
            let mut v=q*cnt-q/3*len+2*l+(if top{-al}else{al})*i32::from(m&back==0)
                +(if top{gc-l}else{-gc-l})*i32::from(old>=0&&(m|old)&back==0);
            let mut ok=true;for j in 0..w{
                for (u,edge) in [(j,old>=0&&(old|m)>>j&1!=0),(w+j-1,j>0&&m>>(j.saturating_sub(1))&3!=0),
                    (2*w,j==0&&(!top||phase==0||m&1!=0))]{
                    if !edge{continue}let b=rt(&p,w+j);let c=rt(&p,u);if b==c{ok=false;break}
                    v-=2*l*i32::from(f[b]&&f[c]);f[b]|=f[c];p[c]=b
                }if !ok{break}
            }
            if ok{let mut ids=[30;20];let mut key=0;let mut ff=0;
                for j in 0..=w{let r=rt(&p,w+j);ids[r]=ids[r].min(j);key|=(ids[r]as u64)<<(4*j);ff|=(f[r]as u16)<<j}
                let s=(m,key,ff,if top{(phase+1)%3}else{0});let n=st.len();let k=*ix.entry(s).or_insert(n as u32);
                if k as usize==n{st.push(s)}arcs.push((k,v as i16));
            }
            if m==0{break}m=(m-1)&free
        }i+=1
    }
    starts.push(arcs.len());let mut z=vec![i32::MIN;i];z[0]=0;let mut maxima=vec![0];
    for _ in 1..=150{
        let mut d=vec![i32::MIN;i];
        for j in 0..i{if z[j]==i32::MIN{continue}for &(k,c) in &arcs[starts[j]..starts[j+1]]{let u=&mut d[k as usize];*u=(*u).max(z[j]+c as i32)}}
        maxima.push(*d.iter().max().unwrap());
        z=d
    }
    for p in 1..=60{let k=maxima[150]-maxima[150-p];
        if !(90..=150).all(|j|maxima[j]-maxima[j-p]==k){continue}
        let mut f=vec![0;i];
        for _ in 0..=i.min(200){
            let mut change=false;
            for j in 0..i{let z=f[j];for &(n,c) in &arcs[starts[j]..starts[j+1]]{
                let u=&mut f[n as usize];let v=z+p as i32*c as i32-k;if v>*u{*u=v;change=true}
            }}
            if !change{println!("end {top} depth {w}, {i} states, certified slope <= {k}/{p}");return}
        }
    }panic!("no verified cycle bound")
}
