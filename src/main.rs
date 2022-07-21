use clap::Parser;
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
use std::path::PathBuf;
use itertools::Itertools;

use lin_inf::lin_graph::*;
use lin_inf::mclique::*;
use lin_inf::permutation::Permutation;
use lin_inf::formula::{Var,Const};

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

#[derive(Parser)]
#[clap(version = "0.1", author = "Alex Rice <aar53@cam.ac.uk>")]
struct Opts {
    #[clap(subcommand)]
    subcmd : SubCommand
}

#[derive(Parser)]
enum SubCommand {
    #[clap(version = "0.1", author = "Alex Rice <aar53@cam.ac.uk>")]
    Search(SearchOpts),
    #[clap(version = "0.1", author = "Alex Rice <aar53@cam.ac.uk>")]
    Latex(LatexOpts),
    #[clap(version = "0.1", author = "Alex Rice <aar53@cam.ac.uk>")]
    Dualise(DualiseOpts),
    #[clap(version = "0.1", author = "Alex Rice <aar53@cam.ac.uk>")]
    Basis(BasisOpts),
    #[clap(version = "0.1", author = "Alex Rice <aar53@cam.ac.uk>")]
    Data(DataOpts)
}

/// Search for underivable inferences
#[derive(Parser,Clone)]
struct SearchOpts {
    /// Number of Variables
    number_vars: usize,

    #[clap(flatten)]
    run_opts: RunOpts,

    /// use switch
    #[clap(short, long)]
    switch: bool,
    /// use medial
    #[clap(short, long)]
    medial: bool,
    #[clap(long)]
    from_file: Option<String>
}

/// Generate basis M_n
#[derive(Parser,Clone)]
struct BasisOpts {
    /// Number of variables to run up to
    number_vars: usize,

    #[clap(flatten)]
    run_opts: RunOpts
}

#[derive(Parser,Clone)]
struct RunOpts {
    /// Do not use cached files
    #[clap(short,long)]
    check: bool,
    /// restrict to p4
    #[clap(short,long)]
    p4: bool,
    /// Use dual notion of implication
    #[clap(short,long)]
    dual: bool,
    /// Do not write to cache
    #[clap(short, long)]
    no_write: bool,
    /// Only print result
    #[clap(short, long)]
    quiet: bool,
}

/// Latexify p4 free graphs
#[derive(Parser,Clone)]
struct LatexOpts {
    /// Number of Variables
    #[clap(short,long)]
    number_vars: Option<usize>,
    /// premise graph
    #[clap(short,long)]
    premise: Option<u128>,
    /// conclusion graph
    #[clap(short,long)]
    conclusion: Option<u128>,
    /// get inferences from file
    #[clap(long)]
    from_file: Option<String>,
    /// Only show graphs
    #[clap(short,long)]
    only_graph: bool
}

/// Display data about given inferences
#[derive(Parser,Clone)]
struct DataOpts {
    /// Number of Variables
    #[clap(short,long)]
    number_vars: Option<usize>,
    /// premise graph
    #[clap(short,long)]
    premise: Option<u128>,
    /// conclusion graph
    #[clap(short,long)]
    conclusion: Option<u128>,
    /// get inferences from file
    #[clap(long)]
    from_file: Option<String>
}

/// Analyse duality of graphs
#[derive(Parser,Clone)]
struct DualiseOpts {
    /// Number of Variables
    #[clap(short,long)]
    number_vars: Option<usize>,
    /// premise graph
    #[clap(short,long)]
    premise: Option<u128>,
    /// conclusion graph
    #[clap(short,long)]
    conclusion: Option<u128>,
    /// get inferences from file
    #[clap(long)]
    from_file: Option<String>,
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
    x: &T,
    xs: &HashMap<T, Vec<U>>,
    number_vars: usize,
    dual: bool
) -> HashSet<T>
where
    T: NumericGraph,
    U: NumericMClique,
{
    if dual {
	let c = &xs[&x.dualise(number_vars)];
	xs.iter()
	    .filter(|(_, c2)| &c != c2 && linear_implication(c2, c) && !is_trivial(c2, c, number_vars))
	    .map(|x| x.0.dualise(number_vars))
	    .collect()
    }
    else {
	let c = &xs[x];
	xs.iter()
            .filter(|(_, c2)| &c != c2 && linear_implication(c, c2) && !is_trivial(c, c2, number_vars))
            .map(|x| x.0.clone())
            .collect()
    }
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
		let path = PathBuf::from(filename);
		fs::create_dir_all(path.parent().unwrap()).unwrap();
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
    dual: bool
) -> InfGraph<T>
where
    T: NumericGraph,
    U: NumericMClique,
{
    least_p4
        .par_iter()
        .progress_with(o.progress(least_p4.len()))
        .map(|a| (*a, build_non_trivial_edges_from(a, &xs, number_vars, dual)))
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

fn run_choose_size(number_vars: usize, rewrites : &Vec<Rewrite>, opts: &RunOpts) -> Vec<(u128,u128)> {
    if number_vars < 9 {
        run::<u32, u8>(number_vars, &rewrites, opts).1.into_iter().map(|(a,b)| (u128::from(a), u128::from(b))).collect()
    } else if number_vars < 12 {
        run::<u64, u16>(number_vars, &rewrites, opts).1.into_iter().map(|(a,b)| (u128::from(a), u128::from(b))).collect()
    } else {
        run::<u128, u16>(number_vars, &rewrites, opts).1
    }
}

fn run<T, U>(
    number_vars: usize,
    rewrites : &Vec<Rewrite>,
    opts: &RunOpts
) -> (Vec<usize>, Vec<(T, T)>)
where
    T: NumericGraph,
    U: NumericMClique,
{
    let RunOpts {
	check,
	no_write,
	quiet,
	p4,
	dual
    } = opts.clone();
    let o = Output(quiet);
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
    let dualstr = if dual { "_dual" } else { "" };
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
        &format!("graphs/inf_graph_least{}{}_{}.json", p4fstr, dualstr, number_vars),
        || build_graph(&mc, &least_graphs, number_vars, &o, dual),
        check,
        no_write,
        &o,
    );

    o.out(&format!(
        "Number of non-trivial-inferences: {}",
        inf_graph.iter().map(|(_, v)| v.len()).sum::<usize>()
    ));

    let min_graph: InfGraph<T> = retrieve_graph(
        &format!("graphs/min_inf_graph{}{}_{}.json", p4fstr, dualstr, number_vars),
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

    // for x in &mut others { *x = reduce_inference(x.0, x.1, number_vars) };
    let others_len = others.len();

    others.par_iter_mut().progress_with(o.progress(others_len)).for_each(|x| {
	*x = reduce_inference(x.0, x.1, number_vars);
    });

    others.sort();
        others.dedup();
    // others.dedup_by_key(|x| x.0);
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
    println!("There were {} other inferences up to isomorphism", others.len());
    (classified, others)
}

fn parse_rewrites(filename: &Option<String>, switch : bool, medial: bool) -> Vec<Rewrite> {
    let mut rewrites : Vec<Rewrite> = vec![];

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

    if let Some(file) = filename {
	let mut input = csv::ReaderBuilder::new()
	    .has_headers(false)
	    .comment(Some(b'#'))
	    .from_path(file)
	    .unwrap();
	for result in input.deserialize() {
	    let record: Rewrite = result.unwrap();
	    rewrites.push(record);
	}
    }

    rewrites
}

fn dualise(rewrite: Rewrite) {
    let Rewrite {
	name,
	size,
	input_graph,
	output_graph,
    } = rewrite;
    if name != "" {
	println!("Analysing {}", name);
    }
    let (a,b) = reduce_inference(input_graph, output_graph, size);
    let (duala, dualb) = (output_graph.dualise(size), input_graph.dualise(size));
    let (ad, bd) = reduce_inference(duala, dualb, size);
    println!("Dualising {} -> {}", input_graph, output_graph);
    println!("Dual is {} -> {}", duala,dualb);
    println!("Original reduces to {} -> {}", a, b);
    println!("Dual reduces to {} -> {}", ad, bd);
    if (a,b) == (ad, bd) {
	println!("{} -> {} is self dual", input_graph, output_graph);
    }
}

fn write_graph_edges<T : LinGraph>(x: &T, size: usize) -> String {
    (0..size).tuple_combinations().map(|(a,b)| { if x.get(a,b) { 'r' } else { 'g' }}).collect()
}

fn into_latex(rewrite: Rewrite, only_graph: bool) {
    let Rewrite {
	name: _,
	size,
	input_graph,
	output_graph,
    } = rewrite;
    if input_graph.p4_free(size) && output_graph.p4_free(size) && !only_graph {
	let premise = input_graph.cograph_decomp(size);
	let conclusion = output_graph.cograph_decomp(size);
	println!(r#"\begin{{equation}}"#);
	println!(""); // for label
	println!(r#"\begin{{alignedat}}{{2}}"#);
	println!(r#"& &&{}\\"#, premise);
	println!(r#"&\to &\quad& {}"#, conclusion);
	println!(r#"\end{{alignedat}}"#);
	println!(r#"\end{{equation}}"#);
    }
    else if !only_graph {
	println!("Input is not p4 free");
    }
    let nodes = (0..size).map(|x| x.to_string()).collect::<Vec<String>>().join(",");
    let graph_command = match size {
	2 => Some("TwoGraph"),
	3 => Some("ThreeGraph"),
	4 => Some("FourGraph"),
	5 => Some("FiveGraph"),
	6 => Some("SixGraph"),
	7 => Some("SevenGraph"),
	8 => Some("EightGraph"),
	9 => Some("NineGraph"),
	_ => None
    };
    if let Some(s) = graph_command {
	if !only_graph { println!("Input graph:") } else { print!(r#"\["#) };
	println!(r#"\{}{{{}}}{}"#, s, nodes, write_graph_edges(&input_graph, size));
	if !only_graph { println!("Output graph:") } else { println!(r#"\quad \to \quad"#)};
	println!(r#"\{}{{{}}}{}{}"#, s, nodes, write_graph_edges(&output_graph, size), if only_graph { r#"\]"# } else { "" });
    }
}

fn get_basis_filename(opts : &RunOpts, number_vars: usize) -> String {
    let RunOpts { check: _, p4, dual, no_write: _, quiet: _ } = opts;
    format!("Basis/basis{}{}_{}", if *p4 { "_p4free" } else { "" }, if *dual { "_dual" } else { "" }, number_vars)
}


fn main() {
    let opts = Opts::parse();
    match opts.subcmd {
	SubCommand::Search(opts) => {
	    let SearchOpts {
		number_vars,
		switch,
		medial,
		from_file,
		run_opts
	    } = &opts;
	    let rewrites = parse_rewrites(from_file,*switch,*medial);
	    run_choose_size(*number_vars, &rewrites, &run_opts);

	},
	SubCommand::Dualise(opts) => {
	    let DualiseOpts { number_vars, premise, conclusion, from_file } = opts;
	    let mut rewrites = parse_rewrites(&from_file, false, false);
	    match (number_vars, premise, conclusion) {
		(Some(nv), Some(p), Some(c)) => {
		    rewrites.push(Rewrite { name: "".to_string(), size: nv, input_graph: p, output_graph: c })
		}
		_ => ()
	    }
	    for r in rewrites {
		dualise(r);
		println!("-----");
	    }
	},
	SubCommand::Latex(opts) => {
	    let LatexOpts { number_vars, premise, conclusion, from_file, only_graph } = opts;
	    let mut rewrites = parse_rewrites(&from_file, false, false);
	    match (number_vars, premise, conclusion) {
		(Some(nv), Some(p), Some(c)) => {
		    rewrites.push(Rewrite { name: "".to_string(), size: nv, input_graph: p, output_graph: c })
		}
		_ => ()
	    }
	    for r in rewrites {
		if !only_graph { println!("{}", r.name) };
		into_latex(r, only_graph);
		println!("")
	    }
	},
	SubCommand::Basis(opts) => {
	    let BasisOpts {
		number_vars,
		run_opts,
		..
	    } = &opts;
	    let mut current_rewrites : Vec<Rewrite> = vec![];
	    for i in 0..=*number_vars {
		println!("---------------");
		println!("Running on {} variables", i);

		let mut new_rewrites : Vec<Rewrite> = run_choose_size(i, &current_rewrites, &run_opts).into_iter().enumerate().map(|(n,(a,b))| Rewrite {
		    name: format!("{}_{}", n, i),
		    size: i,
		    input_graph: a,
		    output_graph: b
		}).collect();
		if ! run_opts.no_write {
		    let data = new_rewrites.iter().map(| Rewrite { name, size, input_graph, output_graph } | format!("{},{},{},{}", name , size,input_graph,output_graph)).collect::<Vec<_>>().join("\n");
		    let filename = get_basis_filename(run_opts, i);
		    let path = PathBuf::from(filename);
		    fs::create_dir_all(path.parent().unwrap()).unwrap();
		    fs::write(get_basis_filename(run_opts, i), data).unwrap();
		}
		current_rewrites.append(&mut new_rewrites)
	    }
	}
	SubCommand::Data(opts) => {
	    let DataOpts {
		number_vars,
		premise,
		conclusion,
		from_file
	    } = opts;
	    let mut rewrites = parse_rewrites(&from_file, false, false);
	    match (number_vars, premise, conclusion) {
		(Some(nv), Some(p), Some(c)) => {
		    rewrites.push(Rewrite { name: "".to_string(), size: nv, input_graph: p, output_graph: c })
		}
		_ => ()
	    }
	    for r in rewrites {
		println!("---------------");
		println!("Inference {}", r.name);
		let in_form = r.input_graph.cograph_decomp(r.size);
		let out_form = r.output_graph.cograph_decomp(r.size);
		println!("Input formula:");
		println!("{}", in_form);
		println!("{} red edges and {} green edges", r.input_graph.edges(r.size), r.input_graph.non_edges(r.size));
		println!("Output formula:");
		println!("{}", out_form);
		println!("{} red edges and {} green edges", r.output_graph.edges(r.size), r.output_graph.non_edges(r.size));
		println!("{} green edges turn red in this inference and {} green edges turn red", non_edge_to_edge(&r.input_graph, &r.output_graph, r.size), edge_to_non_edge(&r.input_graph, &r.output_graph, r.size));
		let basis : Vec<_> = (0..r.size).map( | x | parse_rewrites(&Some(get_basis_filename(&RunOpts { p4: true, check: false, no_write: true, quiet: true, dual: false}, x)),false,false)).collect();
		let mut deduces : Vec<(String, Vec<usize>)>= (0..r.size).map(|_| (0..3)).multi_cartesian_product().map(| v | {
		    let mut v2 = Vec::new();
		    let mut current_var = 0;
		    for x in v.iter() {
		       match x {
			   0 => v2.push(Const(true)),
			   1 => v2.push(Const(false)),
			   _ => {
			       v2.push(Var(current_var));
			       current_var += 1;
			   }
                       }
		    }
		    let f = | x : usize | {
			v2[x].clone()
		    };
		    let left = in_form.map_formula(&f).simplify();
		    let right = out_form.map_formula(&f).simplify();
		    if left.unit_free() && right.unit_free() && left.len() == right.len() && left.len() < r.size {
			let lg1 = u128::from_formula(&left);
			let lg2 = u128::from_formula(&right);
			let (t1, t2) = reduce_inference(lg1 , lg2, left.len());
			let out = basis[left.len()].iter().find(| r2 | r2.size == left.len() && r2.input_graph == t1 && r2.output_graph == t2 ).map(|r| r.name.clone());
			out.map(move |x| (x,v))
		    }
		    else {
			None
		    }
		}).filter_map(| x | x).collect();
		deduces.sort();
		deduces.dedup_by_key(| (x,_) | x.clone());
		for (x, _) in deduces {
		    println! ("deduces {}", x);
		}
	    }
	}
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_5() {
        assert_eq!(
            run::<u32, u8>(5, &parse_rewrites(&None, true, true), &RunOpts {
	     p4: true,
	     check: true,
	     no_write: true,
	     quiet: true,
	     dual: false
	    }),
            (vec![65, 12], vec![])
        )
    }

    #[test]
    fn test_6() {
        assert_eq!(
            run::<u32, u8>(6, &parse_rewrites(&None, true, true), &RunOpts {
	     p4: true,
	     check: true,
	     no_write: true,
	     quiet: true,
	     dual: false
	    }),
            (vec![266, 84], vec![])
        )
    }

    #[test]
    fn test_6_u64() {
        assert_eq!(
            run::<u64, u16>(6, &parse_rewrites(&None, true, true), &RunOpts {
	     p4: true,
	     check: true,
	     no_write: true,
	     quiet: true,
	     dual: false
	    }),
            (vec![266, 84], vec![])
        )
    }
}
