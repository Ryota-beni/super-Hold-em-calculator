// ════════════════════════════════════════════════════════════════
//  Super Hold'em ハンドランキング 完全列挙 equity 計算
//
//   各3枚ハンドについて「ランダムな相手1人(3枚)＋ボード5枚」を
//   全パターン列挙し、勝ち=1 / チョップ=0.5 / 負け=0 の平均(equity)を出す。
//
//   ・カードは 0..51 の整数 (rank = c>>2, suit = c&3)
//   ・スート同型を畳んで 1,755 種の代表ハンドのみ計算
//   ・6コア並列 + 1ハンドごとに results.csv へ追記(中断/再開対応)
//   ・全完了後 ranking.json を出力し、加重平均equity(=0.5のはず)を検算
//
//   使い方:
//     cargo run --release                 … 本計算(再開対応)
//     cargo run --release -- calibrate 2  … 2ハンドだけ単スレ計測して所要時間を推定
// ════════════════════════════════════════════════════════════════

use std::collections::{HashMap, HashSet};
use std::fs::{File, OpenOptions};
use std::io::{BufRead, BufReader, Write};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;
use std::time::Instant;

const P5: i32 = 759375;
const P4: i32 = 50625;
const P3: i32 = 3375;
const P2: i32 = 225;
const P1: i32 = 15;
const P0: i32 = 1;

const RANK_CH: [char; 13] = ['2','3','4','5','6','7','8','9','T','J','Q','K','A'];
const SUIT_CH: [char; 4] = ['♠','♥','♦','♣'];

// ── ストレート事前テーブル: 13bitランクマスク → 最高ストレートのトップランク(なければ-1)
fn build_straight() -> Vec<i8> {
    let mut t = vec![-1i8; 8192];
    for m in 0usize..8192 {
        let mut top: i8 = -1;
        let mut r = 12i32;
        while r >= 4 {
            let b = |x: i32| (m >> x) & 1 == 1;
            if b(r) && b(r-1) && b(r-2) && b(r-3) && b(r-4) { top = r as i8; break; }
            r -= 1;
        }
        // ホイール A-2-3-4-5
        if top < 0 && (m>>12)&1==1 && m&1==1 && (m>>1)&1==1 && (m>>2)&1==1 && (m>>3)&1==1 {
            top = 3;
        }
        t[m] = top;
    }
    t
}

// ── 8枚以下の累積状態
#[derive(Clone, Copy)]
struct St {
    f: [u8; 13],   // ランク頻度
    sm: [u16; 4],  // スート別ランクマスク
    sc: [u8; 4],   // スート別枚数
    rm: u16,       // 全ランクマスク
}
impl St {
    #[inline(always)]
    fn new() -> St { St { f: [0; 13], sm: [0; 4], sc: [0; 4], rm: 0 } }
    #[inline(always)]
    fn add(&mut self, c: u8) {
        let r = (c >> 2) as usize;
        let s = (c & 3) as usize;
        self.f[r] += 1;
        self.sm[s] |= 1u16 << r;
        self.sc[s] += 1;
        self.rm |= 1u16 << r;
    }
}

// ── 最良5枚スコア
#[inline(always)]
fn score(st: &St, straight: &[i8]) -> i32 {
    // フラッシュ
    let fm: i32 = if st.sc[0] >= 5 { st.sm[0] as i32 }
        else if st.sc[1] >= 5 { st.sm[1] as i32 }
        else if st.sc[2] >= 5 { st.sm[2] as i32 }
        else if st.sc[3] >= 5 { st.sm[3] as i32 }
        else { -1 };
    if fm >= 0 {
        let sf = straight[fm as usize];
        if sf >= 0 { return 8 * P5 + (sf as i32) * P4; }
        let mut k = [0i32; 5];
        let mut n = 0;
        let mut r = 12i32;
        while r >= 0 && n < 5 { if (fm >> r) & 1 == 1 { k[n] = r; n += 1; } r -= 1; }
        return 5 * P5 + k[0]*P4 + k[1]*P3 + k[2]*P2 + k[3]*P1 + k[4]*P0;
    }
    // ランク頻度
    let mut q = -1i32; let mut t1 = -1i32; let mut t2 = -1i32; let mut p1 = -1i32; let mut p2 = -1i32;
    let mut r = 12i32;
    while r >= 0 {
        let f = st.f[r as usize];
        if f == 4 { q = r; }
        else if f == 3 { if t1 < 0 { t1 = r; } else { t2 = r; } }
        else if f == 2 { if p1 < 0 { p1 = r; } else if p2 < 0 { p2 = r; } }
        r -= 1;
    }
    if q >= 0 { // フォーカード
        let mut kk = -1i32; let mut r = 12i32;
        while r >= 0 { if r != q && st.f[r as usize] > 0 { kk = r; break; } r -= 1; }
        return 7*P5 + q*P4 + kk*P3;
    }
    if t1 >= 0 && (t2 >= 0 || p1 >= 0) { // フルハウス
        let p = if t2 >= 0 { t2 } else { p1 };
        return 6*P5 + t1*P4 + p*P3;
    }
    let s = straight[st.rm as usize]; // ストレート
    if s >= 0 { return 4*P5 + (s as i32)*P4; }
    if t1 >= 0 { // スリーカード
        let mut a = -1i32; let mut b = -1i32; let mut r = 12i32;
        while r >= 0 { if r != t1 && st.f[r as usize] > 0 { if a < 0 { a = r; } else { b = r; break; } } r -= 1; }
        return 3*P5 + t1*P4 + a*P3 + b*P2;
    }
    if p1 >= 0 && p2 >= 0 { // ツーペア
        let mut kk = -1i32; let mut r = 12i32;
        while r >= 0 { if r != p1 && r != p2 && st.f[r as usize] > 0 { kk = r; break; } r -= 1; }
        return 2*P5 + p1*P4 + p2*P3 + kk*P2;
    }
    if p1 >= 0 { // ワンペア
        let mut a = -1i32; let mut b = -1i32; let mut d = -1i32; let mut r = 12i32;
        while r >= 0 { if r != p1 && st.f[r as usize] > 0 { if a < 0 { a = r; } else if b < 0 { b = r; } else { d = r; break; } } r -= 1; }
        return 1*P5 + p1*P4 + a*P3 + b*P2 + d*P1;
    }
    // ハイカード
    let mut h = [0i32; 5]; let mut n = 0; let mut r = 12i32;
    while r >= 0 && n < 5 { if st.f[r as usize] > 0 { h[n] = r; n += 1; } r -= 1; }
    h[0]*P4 + h[1]*P3 + h[2]*P2 + h[3]*P1 + h[4]*P0
}

// ── 1ハンドの equity を完全列挙
fn equity(hero: [u8; 3], straight: &[i8]) -> f64 {
    // 残り49枚
    let mut rem = [0u8; 49];
    let mut idx = 0;
    for c in 0u8..52 {
        if c != hero[0] && c != hero[1] && c != hero[2] { rem[idx] = c; idx += 1; }
    }
    let mut win: u64 = 0;
    let mut tie: u64 = 0;
    let mut tot: u64 = 0;

    // ボード 5/49
    for a in 0..49 { for b in (a+1)..49 { for c in (b+1)..49 { for d in (c+1)..49 { for e in (d+1)..49 {
        let mut bs = St::new();
        bs.add(rem[a]); bs.add(rem[b]); bs.add(rem[c]); bs.add(rem[d]); bs.add(rem[e]);

        // ヒーロー役(ボード+ヒーロー3)
        let mut hs = bs;
        hs.add(hero[0]); hs.add(hero[1]); hs.add(hero[2]);
        let hv = score(&hs, straight);

        // 相手プール(44枚) = rem からボード5枚を除外
        let mut pool = [0u8; 44];
        let mut pn = 0;
        for i in 0..49 {
            if i == a || i == b || i == c || i == d || i == e { continue; }
            pool[pn] = rem[i]; pn += 1;
        }

        // 相手 3/44
        for x in 0..44 { for y in (x+1)..44 { for z in (y+1)..44 {
            let mut os = bs;
            os.add(pool[x]); os.add(pool[y]); os.add(pool[z]);
            let ov = score(&os, straight);
            tot += 1;
            if hv > ov { win += 1; } else if hv == ov { tie += 1; }
        }}}
    }}}}}

    (win as f64 + 0.5 * tie as f64) / tot as f64
}

// ── 4要素の全順列(24通り)
fn perms4() -> Vec<[u8; 4]> {
    let mut out = Vec::new();
    let a = [0u8, 1, 2, 3];
    for i in 0..4 { for j in 0..4 { if j==i {continue;} for k in 0..4 { if k==i||k==j {continue;} for l in 0..4 { if l==i||l==j||l==k {continue;} out.push([a[i],a[j],a[k],a[l]]); }}}}
    out
}

// ── 3枚ハンドをスート同型で正規化(全24順列のうち辞書順最小)
fn canonical(combo: [u8; 3], perms: &[[u8; 4]]) -> [u8; 3] {
    let mut best: Option<[u8; 3]> = None;
    for p in perms {
        let mut m = [0u8; 3];
        for i in 0..3 {
            let c = combo[i];
            let r = c >> 2;
            let s = (c & 3) as usize;
            m[i] = (r << 2) | p[s];
        }
        m.sort_unstable();
        if best.is_none() || m < best.unwrap() { best = Some(m); }
    }
    best.unwrap()
}

fn card_str(c: u8) -> String {
    format!("{}{}", RANK_CH[(c >> 2) as usize], SUIT_CH[(c & 3) as usize])
}

fn hand_str(h: [u8; 3]) -> String {
    // ランク降順で表示
    let mut v = [h[0], h[1], h[2]];
    v.sort_unstable_by(|a, b| b.cmp(a));
    format!("{}{}{}", card_str(v[0]), card_str(v[1]), card_str(v[2]))
}

// スートパターン分類
fn suit_type(h: [u8; 3]) -> &'static str {
    let r = [h[0]>>2, h[1]>>2, h[2]>>2];
    let s = [h[0]&3, h[1]&3, h[2]&3];
    let distinct_ranks = !(r[0]==r[1] || r[1]==r[2] || r[0]==r[2]) || (r[0]!=r[1]&&r[1]!=r[2]&&r[0]!=r[2]);
    let all_same_rank = r[0]==r[1] && r[1]==r[2];
    let pair = (r[0]==r[1])||(r[1]==r[2])||(r[0]==r[2]);
    if all_same_rank { return "trips"; }
    if pair {
        // ペア+キッカー: キッカーがペアと同スートか
        // ペアのランク特定
        let pr = if r[0]==r[1] {r[0]} else if r[1]==r[2] {r[1]} else {r[0]};
        let mut pair_suits = vec![];
        let mut kick_suit = 0u8;
        for i in 0..3 { if r[i]==pr { pair_suits.push(s[i]); } else { kick_suit = s[i]; } }
        if pair_suits.contains(&kick_suit) { "pair-suited" } else { "pair-offsuit" }
    } else {
        let _ = distinct_ranks;
        let su: HashSet<u8> = s.iter().cloned().collect();
        match su.len() { 1 => "monotone", 2 => "two-tone", _ => "rainbow" }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let straight = build_straight();

    // 代表ハンド(1755種)とその出現数を生成
    let perms = perms4();
    let mut map: HashMap<[u8; 3], u32> = HashMap::new();
    for i in 0u8..52 { for j in (i+1)..52 { for k in (j+1)..52 {
        let canon = canonical([i, j, k], &perms);
        *map.entry(canon).or_insert(0) += 1;
    }}}
    let mut reps: Vec<([u8; 3], u32)> = map.into_iter().collect();
    reps.sort_unstable();
    let total_combos: u32 = reps.iter().map(|x| x.1).sum();
    eprintln!("代表ハンド数: {} / 実組み合わせ合計: {} (期待値 1755 / 22100)", reps.len(), total_combos);
    assert_eq!(reps.len(), 1755);
    assert_eq!(total_combos, 22100);

    // ── calibrate モード
    if args.len() >= 2 && args[1] == "calibrate" {
        let k: usize = if args.len() >= 3 { args[2].parse().unwrap_or(2) } else { 2 };
        let cores = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1);
        eprintln!("calibrate: 先頭{}ハンドを単スレッドで計測...", k);
        let t0 = Instant::now();
        for i in 0..k {
            let (h, m) = reps[i];
            let tt = Instant::now();
            let eq = equity(h, &straight);
            eprintln!("  {} (x{}) equity={:.4}  {:.1}秒", hand_str(h), m, eq, tt.elapsed().as_secs_f64());
        }
        let per = t0.elapsed().as_secs_f64() / k as f64;
        let total_1core = per * 1755.0;
        eprintln!("\n1ハンド平均: {:.1}秒", per);
        eprintln!("全1755ハンド見積り:");
        eprintln!("  1コア : {:.1}時間", total_1core / 3600.0);
        eprintln!("  {}コア: {:.1}時間", cores, total_1core / 3600.0 / cores as f64);
        return;
    }

    // ── 本計算(再開対応)
    let out_path = "results.csv";
    let mut done: HashSet<[u8; 3]> = HashSet::new();
    if let Ok(f) = File::open(out_path) {
        for line in BufReader::new(f).lines().flatten() {
            let parts: Vec<&str> = line.split(',').collect();
            if parts.len() >= 3 {
                if let (Ok(a), Ok(b), Ok(c)) = (parts[0].parse::<u8>(), parts[1].parse::<u8>(), parts[2].parse::<u8>()) {
                    done.insert([a, b, c]);
                }
            }
        }
    }
    eprintln!("既に完了: {} ハンド / 残り: {}", done.len(), 1755 - done.len());

    let pending: Vec<([u8; 3], u32)> = reps.iter().cloned().filter(|(h, _)| !done.contains(h)).collect();
    if pending.is_empty() {
        eprintln!("全ハンド計算済み。ランキングを生成します。");
        write_ranking(&reps, out_path);
        return;
    }

    let cores = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1);
    eprintln!("{}コアで計算開始 (残り{}ハンド)", cores, pending.len());

    let file = OpenOptions::new().create(true).append(true).open(out_path).unwrap();
    let writer = Mutex::new(file);
    let counter = AtomicUsize::new(0);
    let completed = AtomicUsize::new(done.len());
    let start = Instant::now();

    std::thread::scope(|scope| {
        for _ in 0..cores {
            scope.spawn(|| {
                loop {
                    let i = counter.fetch_add(1, Ordering::Relaxed);
                    if i >= pending.len() { break; }
                    let (h, m) = pending[i];
                    let eq = equity(h, &straight);
                    {
                        let mut w = writer.lock().unwrap();
                        writeln!(w, "{},{},{},{},{:.8}", h[0], h[1], h[2], m, eq).unwrap();
                        w.flush().unwrap();
                    }
                    let c = completed.fetch_add(1, Ordering::Relaxed) + 1;
                    let el = start.elapsed().as_secs_f64();
                    let rate = (c - done.len()) as f64 / el.max(0.001);
                    let eta = (1755 - c) as f64 / rate.max(1e-9);
                    eprintln!("[{}/1755] {} eq={:.4}  経過{:.1}分 ETA{:.1}分",
                        c, hand_str(h), eq, el/60.0, eta/60.0);
                }
            });
        }
    });

    eprintln!("\n計算完了。ランキングを生成します。");
    write_ranking(&reps, out_path);
}

// results.csv を読んでランキングを出力
fn write_ranking(reps: &[([u8; 3], u32)], out_path: &str) {
    let mut eqmap: HashMap<[u8; 3], (u32, f64)> = HashMap::new();
    if let Ok(f) = File::open(out_path) {
        for line in BufReader::new(f).lines().flatten() {
            let p: Vec<&str> = line.split(',').collect();
            if p.len() >= 5 {
                if let (Ok(a), Ok(b), Ok(c), Ok(m), Ok(eq)) =
                    (p[0].parse::<u8>(), p[1].parse::<u8>(), p[2].parse::<u8>(), p[3].parse::<u32>(), p[4].parse::<f64>()) {
                    eqmap.insert([a, b, c], (m, eq));
                }
            }
        }
    }
    if eqmap.len() != reps.len() {
        eprintln!("警告: 完了 {} / 全 {} 。まだ未完了です。", eqmap.len(), reps.len());
        return;
    }

    let mut rows: Vec<([u8; 3], u32, f64)> = eqmap.iter().map(|(k, v)| (*k, v.0, v.1)).collect();
    rows.sort_by(|a, b| b.2.partial_cmp(&a.2).unwrap());

    // 加重平均equity(=0.5検算)
    let wsum: f64 = rows.iter().map(|r| r.2 * r.1 as f64).sum();
    let wmean = wsum / 22100.0;
    eprintln!("加重平均equity = {:.6}  (対称性より 0.5 になるはず)", wmean);

    // JSON出力
    let mut json = String::from("[\n");
    let mut cum: u64 = 0;
    for (rank, (h, m, eq)) in rows.iter().enumerate() {
        cum += *m as u64;
        let percentile = 100.0 * cum as f64 / 22100.0; // 上位%(最強≈0.02, 最弱=100)
        json.push_str(&format!(
            "  {{\"rank\":{},\"hand\":\"{}\",\"cards\":[{},{},{}],\"suitType\":\"{}\",\"combos\":{},\"equity\":{:.6},\"topPercent\":{:.2}}}{}\n",
            rank + 1, hand_str(*h), h[0], h[1], h[2], suit_type(*h), m, eq, percentile,
            if rank + 1 == rows.len() { "" } else { "," }
        ));
    }
    json.push_str("]\n");
    let mut f = File::create("ranking.json").unwrap();
    f.write_all(json.as_bytes()).unwrap();
    eprintln!("ranking.json を出力しました ({} ハンド)", rows.len());

    // 上位/下位を表示
    eprintln!("\n=== 強い順 TOP10 ===");
    for i in 0..10.min(rows.len()) {
        eprintln!("  {:>4}. {}  equity {:.2}%  (x{})", i+1, hand_str(rows[i].0), rows[i].2*100.0, rows[i].1);
    }
    eprintln!("=== 弱い順 BOTTOM5 ===");
    for i in (rows.len()-5)..rows.len() {
        eprintln!("  {:>4}. {}  equity {:.2}%  (x{})", i+1, hand_str(rows[i].0), rows[i].2*100.0, rows[i].1);
    }
}
