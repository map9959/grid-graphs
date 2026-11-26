// Arithmetic only: for each row store the smallest established suffix start.
fn main() {
    let mut count = 0;
    for k in (207usize..2000).step_by(14) {
        for q in (57..k-1).step_by(2) {
            let y = (q-15)/6;
            assert!([13,15,17].contains(&(q-6*y-2)));
            let mut front = vec![k+1;k+1];
            front[y+6]=q-3*y+3;
            let mut closed=false;
            for j in y+6..k-12 {
                let f=front[j];
                if f>k {continue}
                let h=k-j;
                if (14..=43).contains(&h) && k-f>=3*h/4+3 {
                    closed=true;break
                }
                for (s,d,w,height,root) in [(6,4,5,13,false),(13,7,8,20,false),
                    (20,10,11,27,false),(27,13,14,34,false),(4,3,10,10,true)] {
                    let x=if root {f.max(q+1)} else {f};
                    if x+w-1>k-8 || (!root && x+w-1>q) || h<height+7 {continue}
                    front[j+s]=front[j+s].min(x+d);
                }
            }
            assert!(closed,"k={k} q={q}");
            count+=1;
        }
    }
    println!("{count} isolate/size pairs covered by local speed arithmetic");
}
