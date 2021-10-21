use clap::Clap;
use indicatif::{ParallelProgressIterator, ProgressBar};
use rayon::prelude::*;
use serde::de::DeserializeOwned;
use serde::Deserialize;
use serde::Serialize;
use serde_json;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt::Display;
use std::format;
use std::fs;
use std::hash::Hash;
use itertools::Itertools;

use lin_inf::lin_graph::*;
use lin_inf::mclique::*;
use lin_inf::permutation::Permutation;
use lin_inf::formula::Var;

trait NumericGraph:
    LinGraph + Ord + Hash + Send + Sync + Clone + Copy + Display + Serialize + DeserializeOwned
{
}

impl NumericGraph for u32 {}
impl NumericGraph for u64 {}
impl NumericGraph for u128 {}

trait NumericMClique: MClique + Send + Sync + Serialize + DeserializeOwned + PartialEq {}

impl NumericMClique for u8 {}
impl NumericMClique for u16 {}

struct Output(bool);

impl Output {
    fn out(&self, o: &str) {
        if !self.0 {
            println!("{}", o);
        }
    }
    fn progress(&self, len: usize) -> ProgressBar {
        if self.0 {
            ProgressBar::hidden()
        } else {
            ProgressBar::new(len as u64)
        }
    }
}

#[derive(Debug, Deserialize)]
struct Rewrite {
    name: String,
    size: usize,
    #[serde(rename="input")]
    input_graph: u128,
    #[serde(rename="output")]
    output_graph: u128
}

#[derive(Clap)]
#[clap(version = "0.1", author = "Alex Rice <aar53@cam.ac.uk>")]
struct Opts {
    /// Number of Variables
    number_vars: usize,
    /// Run for all variables up to number_vars
    #[clap(short, long)]
    all: bool,
    /// Do not use cached files
    #[clap(short, long)]
    check: bool,
    /// Do not write to cache
    #[clap(short, long)]
    no_write: bool,
    /// Only print result
    #[clap(short, long)]
    quiet: bool,
    /// use switch
    #[clap(short, long)]
    switch: bool,
    /// use medial
    #[clap(short, long)]
    medial: bool,
    /// restrict to p4
    #[clap(short, long)]
    p4: bool,
    /// from file
    #[clap(long)]
    from_file: Option<String>
}

fn all_max_cliques<T, U>(xs: &Vec<T>, number_vars: usize, o: &Output) -> HashMap<T, Vec<U>>
where
    T: NumericGraph,
    U: NumericMClique,
{
    xs.par_iter()
        .progress_with(o.progress(xs.len()))
        .map(|&x| (x, x.max_cliques(number_vars)))
        .collect()
}

fn build_non_trivial_edges_from<T, U>(
    c: &Vec<U>,
    xs: &HashMap<T, Vec<U>>,
    number_vars: usize,
) -> HashSet<T>
where
    T: NumericGraph,
    U: NumericMClique,
{
    xs.iter()
        .filter(|(_, c2)| &c != c2 && linear_implication(c, c2) && !is_trivial(c, c2, number_vars))
        .map(|x| x.0.clone())
        .collect()
}

type InfGraph<T> = HashMap<T, HashSet<T>>;

fn retrieve_graph<U, D: Serialize + DeserializeOwned>(
    filename: &str,
    builder: U,
    check: bool,
    no_write: bool,
    o: &Output,
) -> D
where
    U: FnOnce() -> D,
{
    if let (false, Ok(b)) = (check, fs::read_to_string(filename)) {
        o.out(&format!("Reading file '{}'", filename));
        serde_json::from_str(&b).unwrap()
    } else {
        {
                if check {
                    o.out(&format!("Building {} now...", filename))
                } else {
                    o.out(&format!(
                        "Could not read file '{}', building now...",
                        filename
                    ));
                }
                let b = builder();
                if !no_write {
                    fs::write(filename, serde_json::to_string(&b).unwrap()).unwrap();
                }
                b
            }
    }
}

fn build_graph<T, U>(
    xs: &HashMap<T, Vec<U>>,
    least_p4: &Vec<T>,
    number_vars: usize,
    o: &Output,
) -> InfGraph<T>
where
    T: NumericGraph,
    U: NumericMClique,
{
    least_p4
        .par_iter()
        .progress_with(o.progress(least_p4.len()))
        .map(|a| (*a, build_non_trivial_edges_from(&xs[a], &xs, number_vars)))
        .collect()
}

fn get_minimal<T>(i: &InfGraph<T>, x: T, least_map: &HashMap<T, (T, Permutation)>) -> HashSet<T>
where
    T: NumericGraph,
{
    let keys = i.get(&x);
    match keys {
        None => HashSet::new(),
        Some(k) => {
            let empty = HashSet::new();
            let trans_implied = k.iter().fold(empty.clone(), |acc, y| {
                let (least, perm) = &least_map[y];
                let inv = perm.invert();
                acc.union(&i[&least].iter().map(|x| x.apply_perm(&inv)).collect())
                    .cloned()
                    .collect()
            });
            k.difference(&trans_implied).cloned().collect()
        }
    }
}

fn build_least_map<T>(
    mut p4: Vec<T>,
    number_vars: usize,
    o: &Output,
) -> HashMap<T, (T, Permutation)>
where
    T: NumericGraph,
{
    p4.sort();
    let mut map: HashMap<T, (T, Permutation)> = HashMap::new();
    let perm_vec = Permutation::get_all(number_vars).collect::<Vec<_>>();
    let bar = o.progress(p4.len());
    for l in p4 {
        map.insert(l, (l, Permutation::id(number_vars)));
        for perm in perm_vec.iter() {
            let new = l.apply_perm(perm);
            if new < l {
                let (least, least_perm) = map[&new].clone();
                map.insert(l, (least, least_perm.after(&perm)));
                break;
            }
        }
        bar.inc(1);
    }
    bar.finish_and_clear();
    map
}

fn run_choose_size(number_vars: usize, check: bool, no_write: bool, o: Output, p4 : bool, rewrites : &Vec<Rewrite>) {
    if number_vars < 9 {
        run::<u32, u8>(number_vars, check, no_write, o, p4, &rewrites);
    } else if number_vars < 12 {
        run::<u64, u16>(number_vars, check, no_write, o, p4, &rewrites);
    } else {
        run::<u128, u16>(number_vars, check, no_write, o, p4, &rewrites);
    }
}

fn run<T, U>(
    number_vars: usize,
    check: bool,
    no_write: bool,
    o: Output,
    p4: bool,
    rewrites : &Vec<Rewrite>
) -> (Vec<usize>, Vec<(T, T)>)
where
    T: NumericGraph,
    U: NumericMClique,
{
    let graphs = if p4 {
     	let mut all_p4 = retrieve_graph(
	    &format!("graphs/p4_free_{}.json", number_vars),
            || T::all_p4_free(number_vars),
            check,
            no_write,
            &o,
	);
	all_p4.sort();
	all_p4
    } else {
	T::all_graphs(number_vars)
    };
    let p4str = if p4 { " p4 free" } else { "" };
    let p4fstr = if p4 { "_p4" } else { "" };
    o.out(&format!("Number of{} graphs: {}", p4str, graphs.len()));

    let least_map: HashMap<T, (T, Permutation)> = retrieve_graph(
        &format!("graphs/least_map{}_{}.json", p4fstr, number_vars),
        || build_least_map(graphs.clone(), number_vars, &o),
        check,
        no_write,
        &o,
    );

    let least_graphs: Vec<T> = graphs
        .iter()
        .cloned()
        .filter(|x| least_map.get(x).unwrap().0 == *x)
        .collect();

    o.out(&format!("Number of least{} graphs: {}", p4str, least_graphs.len()));

    let mc = retrieve_graph(
        &format!("graphs/max_cliques{}_{}.json", p4fstr, number_vars),
        || all_max_cliques::<T, U>(&graphs, number_vars, &o),
        check,
        no_write,
        &o,
    );

    o.out(&format!(
        "Number of max cliques: {}",
        mc.iter().map(|(_, y)| y.len()).sum::<usize>()
    ));

    let inf_graph = retrieve_graph(
        &format!("graphs/inf_graph_least{}_{}.json", p4fstr, number_vars),
        || build_graph(&mc, &least_graphs, number_vars, &o),
        check,
        no_write,
        &o,
    );

    o.out(&format!(
        "Number of non-trivial-inferences: {}",
        inf_graph.iter().map(|(_, v)| v.len()).sum::<usize>()
    ));

    let min_graph: InfGraph<T> = retrieve_graph(
        &format!("graphs/min_inf_graph{}_{}.json", p4fstr, number_vars),
        || {
            least_graphs
                .par_iter()
                .progress_with(o.progress(least_graphs.len()))
                .map(|&k| (k, get_minimal(&inf_graph, k, &least_map)))
                .collect()
        },
        check,
        no_write,
        &o,
    );

    let min_infs = min_graph.values().map(|x| x.len()).sum::<usize>();
    o.out(&format!("Number of minimal inferences: {}", min_infs));
    o.out(&format!("Checking inferences..."));


    let (classified, mut others) = min_graph
        .par_iter()
        .progress_with(o.progress(least_graphs.len()))
        .map(|(k, set)| {
	    let mut v : Vec<usize> = (0..rewrites.len()).map(|_| 0).collect();
	    let mut o: Vec<(T, T)> = vec![];
	    for x in set.into_iter() {
		match (0..rewrites.len()).find(|i|{
		    let Rewrite { name: _, size, input_graph, output_graph } = &rewrites[*i];
		    is_rewrite(k, x, input_graph, output_graph, number_vars, *size)
		}) {
		    Some(i) => {v[i] += 1}
		    None => {o.push((*k, *x))}
		}
	    }
	    (v,o)
        })
        .reduce_with(|(v1, mut c), (v2, mut z)| {
            c.append(&mut z);
            (v1.iter().zip(v2).map(|(a,b)| a + b).collect(), c)
        })
        .unwrap_or(((0..rewrites.len()).map(|_| 0).collect(), vec![]));

    others.sort();
    let others_len = others.len();
    others.dedup_by_key(|x| x.0);
    for (k, x) in others.iter() {
        o.out(&format!("----"));
        o.out(&format!("{}", k));
        if p4 {o.out(&format!("{}", k.cograph_decomp(number_vars)))};
        o.out(&format!("",));
        o.out(&format!("{}", x));
        if p4 {o.out(&format!("{}", x.cograph_decomp(number_vars)))};
        o.out(&format!(""));
    }
    println!(
        "There were {} and {} other inferences",
        classified.iter().enumerate().map(|(n,num)| {
	    format!("{} {},", num, rewrites[n].name)
	}).join(" "),
        others_len
    );
    (classified, others)
}

fn parse_rewrites(filename: Option<String>, switch : bool, medial: bool) -> Vec<Rewrite> {
    let mut rewrites : Vec<Rewrite> = vec![];

    if let Some(file) = filename {
	println!("File: {}", file);
	let mut input = csv::ReaderBuilder::new().has_headers(false).from_path(file).unwrap();
	for result in input.deserialize() {
	    let record: Rewrite = result.unwrap();
	    println!("{:?}", record);
	    rewrites.push(record);
	}
    }

    if switch {
	rewrites.push(Rewrite {
	    name: "switches".to_string(),
	    size: 3,
	    input_graph: u128::from_formula(&Var(0).and(Var(1).or(Var(2)))),
	    output_graph: u128::from_formula(&(Var(0).and(Var(1))).or(Var(2)))
	})
    }

    if medial {
	rewrites.push(Rewrite {
	    name: "medials".to_string(),
	    size: 4,
	    input_graph: u128::from_formula(&(Var(0).and(Var(1))).or(Var(2).and(Var(3)))),
	    output_graph: u128::from_formula(&(Var(0).or(Var(2))).and(Var(1).or(Var(3))))
	})
    }
    rewrites
}


fn main() {
    let Opts {
        number_vars,
        all,
        check,
        no_write,
        quiet,
	switch,
	medial,
	p4,
	from_file
    } = Opts::parse();
    let rewrites = parse_rewrites(from_file,switch,medial);
    if all {
        for x in 0..=number_vars {
            run_choose_size(x, check, no_write, Output(quiet), p4, &rewrites);
        }
    } else {
        run_choose_size(number_vars, check, no_write, Output(quiet), p4, &rewrites);
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_5() {
        assert_eq!(
            run::<u32, u8>(5, true, true, Output(true), true),
            (65, 12, vec![])
        )
    }

    #[test]
    fn test_6() {
        assert_eq!(
            run::<u32, u8>(6, true, true, Output(true), true),
            (266, 84, vec![])
        )
    }

    #[test]
    fn test_6_u64() {
        assert_eq!(
            run::<u64, u16>(6, true, true, Output(true), true),
            (266, 84, vec![])
        )
    }
}
