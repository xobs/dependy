extern crate daggy;
extern crate petgraph;

use self::daggy::{Dag, Walker, NodeIndex};
use petgraph::dot::Dot;

use std::collections::HashMap;
use std::fmt;
use std::fs::File;
use std::hash::Hash;
use std::io::Write;
use std::io;

#[derive(Debug)]
pub enum DepError<K> where K: Clone {
    RequirementsNotFound(K),
    RequirementNotFound(K, K),
    SuggestionsNotFound(K),
    SuggestionNotFound(K, K),
    DependencyNotFound(K),
    CircularDependency(K, K),
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum DepEdge {
    /// Dependency B Requires dependency A, and a failure of A
    /// prevents B from running
    Requires,

    /// Dependency B Suggests dependency A, and a failure of A
    Suggests,

    /// Dependency B follows dependency A in the list
    Follows,
}
impl fmt::Display for DepEdge {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &DepEdge::Requires => write!(f, "Requires"),
            &DepEdge::Suggests => write!(f, "Suggests"),
            &DepEdge::Follows => write!(f, "Follows"),
        }
    }
}

pub trait Dependency<K> where K: Clone + Eq + Hash {
    fn name(&self) -> &K;
    fn requirements(&self) -> &Vec<K>;
    fn suggestions(&self) -> &Vec<K>;
    fn provides(&self) -> &Vec<K>;
}

#[derive(Debug, Clone)]
pub struct InternalDependency<K> where K: Clone + Eq + Hash {
    name: K,
    requirements: Vec<K>,
    suggestions: Vec<K>,
    provides: Vec<K>,
}
impl<K> Dependency<K> for InternalDependency<K> where K: Clone + Eq + Hash {
    fn name(&self) -> &K {
        &self.name
    }
    fn requirements(&self) -> &Vec<K> {
        &self.requirements
    }
    fn suggestions(&self) -> &Vec<K> {
        &self.suggestions
    }
    fn provides(&self) -> &Vec<K> {
        &self.provides
    }
}
#[derive(Debug)]
pub struct Dependy<K> where K: Clone + Eq + Hash {
    /// The graph structure, which we will iterate over.
    graph: Dag<K, DepEdge>,

    /// A hashmap containing all nodes in the graph, indexed by name.
    node_bucket: HashMap<K, NodeIndex>,

    /// Whether results were successful or not.
    results: HashMap<K, bool>,

    /// A mapping of "provides" to actual names.
    provides_map: HashMap<K, K>,

    requirements: HashMap<K, Vec<K>>,
    suggestions: HashMap<K, Vec<K>>,

    /// Useed for testing, and making sure the graph is sane.
    dep_map: HashMap<K, InternalDependency<K>>,
}

impl<K> Dependy<K> where K: Clone + Eq + Hash + fmt::Display {
    pub fn new() -> Dependy<K> {
        Dependy {
            graph: Dag::new(),
            node_bucket: HashMap::new(),
            results: HashMap::new(),
            requirements: HashMap::new(),
            suggestions: HashMap::new(),
            provides_map: HashMap::new(),
            dep_map: HashMap::new(),
        }
    }

    pub fn add_dependency<T: Dependency<K>>(&mut self, dependency: &T) {
        let name = dependency.name().clone();
        let new_node = self.graph.add_node(name.clone());
        self.node_bucket.insert(name.clone(), new_node.clone());

        let sd = InternalDependency {
            name: dependency.name().clone(),
            requirements: dependency.requirements().clone(),
            suggestions: dependency.suggestions().clone(),
            provides: dependency.provides().clone(),
        };
        self.dep_map.insert(name.clone(), sd);

        // Also add aliases
        self.provides_map.insert(name.clone(), name.clone());
        for alias in dependency.provides() {
            self.node_bucket.insert(alias.clone(), new_node.clone());
            self.provides_map.insert(alias.clone(), name.clone());
        }

        self.suggestions.insert(name.clone(), dependency.suggestions().clone());
        self.requirements.insert(name.clone(), dependency.requirements().clone());
    }

    pub fn resolve_named_dependencies(&mut self,
                                      dependencies: &Vec<K>)
                                      -> Result<Vec<K>, DepError<K>> {

        let mut to_resolve = dependencies.clone();

        loop {
            if to_resolve.is_empty() {
                break;
            }

            // If this dep_name has been resolved, skip it.
            let dep_name = to_resolve.remove(0);
            let dep_name = match self.provides_map.get(&dep_name) {
                Some(s) => s.clone(),
                None => return Err(DepError::DependencyNotFound(dep_name.clone())),
            };

            // Resolve all requirements.
            match self.requirements.get(&dep_name) {
                None => return Err(DepError::RequirementsNotFound(dep_name.clone())),
                Some(ref reqs) => {
                    for req in *reqs {
                        to_resolve.push(req.clone());
                        let target = match self.node_bucket.get(req) {
                            None => {
                                return Err(DepError::RequirementNotFound(dep_name, req.clone()))
                            }
                            Some(e) => e,
                        };

                        // Don't add extra edges.
                        if self.graph.find_edge(*target, self.node_bucket[&dep_name]).is_some() {
                            continue;
                        }

                        if let Err(_) = self.graph
                            .add_edge(*target, self.node_bucket[&dep_name], DepEdge::Requires) {
                            return Err(DepError::CircularDependency(dep_name.clone(), req.clone()));
                        }
                    }
                }
            }

            // Also resolve all suggestions.
            match self.suggestions.get(&dep_name) {
                None => return Err(DepError::SuggestionsNotFound(dep_name.clone())),
                Some(ref reqs) => {
                    for req in *reqs {
                        to_resolve.push(req.clone());
                        let target = match self.node_bucket.get(req) {
                            None => return Err(DepError::SuggestionNotFound(dep_name, req.clone())),
                            Some(e) => e,
                        };

                        // Don't add extra edges.
                        if self.graph.find_edge(*target, self.node_bucket[&dep_name]).is_some() {
                            continue;
                        }

                        if let Err(_) = self.graph
                            .add_edge(*target, self.node_bucket[&dep_name], DepEdge::Suggests) {
                            return Err(DepError::CircularDependency(dep_name.clone(), req.clone()));
                        }
                    }
                }
            }
        }

        // Add "Follows" dependencies, if no other dependency exists.
        let num_deps = dependencies.len();
        for i in 1..num_deps {
            let previous_dep = dependencies[i - 1].clone();
            let this_dep = dependencies[i].clone();

            let previous_edge = match self.node_bucket.get(&previous_dep) {
                Some(s) => s,
                None => return Err(DepError::DependencyNotFound(previous_dep)),
            };
            let this_edge = match self.node_bucket.get(&this_dep) {
                Some(s) => s,
                None => return Err(DepError::DependencyNotFound(this_dep)),
            };

            // Don't add a "Follows" dependency if one already exists.
            if self.graph.find_edge(*previous_edge, *this_edge).is_some() {
                continue;
            }

            // If we get a "CircularDependency", that's fine, we just won't add this edge.
            self.graph.add_edge(*previous_edge, *this_edge, DepEdge::Follows).ok();
        }

        // Sort everything into a "dependency order"
        let mut dep_order = vec![];
        let mut seen_nodes = HashMap::new();
        for dep_name in dependencies {

            // Pick a node from the bucket and visit it.  This will cause
            // all nodes in the graph to be visited, in order.
            let some_node = self.node_bucket.get(dep_name).unwrap().clone();
            self.visit_node(&mut seen_nodes, &some_node, &mut dep_order);
        }
        Ok(dep_order)
    }

    pub fn resolve_dependencies<T: Dependency<K>>(&mut self,
                                               dependencies: Vec<T>)
                                               -> Result<Vec<K>, DepError<K>> {
        let mut to_resolve = vec![];
        for dep in &dependencies {
            to_resolve.push(dep.name().clone());
        }
        self.resolve_named_dependencies(&to_resolve)
    }

    pub fn save_dot(&self, output: &mut File) -> io::Result<()> {
        write!(output, "{}", Dot::new(self.graph.graph()))
    }

    fn visit_node(&mut self,
                  seen_nodes: &mut HashMap<NodeIndex, ()>,
                  node: &NodeIndex,
                  dep_order: &mut Vec<K>) {

        // If this node has been seen already, don't re-visit it.
        if seen_nodes.insert(node.clone(), ()).is_some() {
            return;
        }

        // 1. Visit all parents
        // 2. Visit ourselves
        // 3. Visit all children

        let parents = self.graph.parents(*node);
        let mut to_visit = vec![];
        for (_, parent_index) in parents.iter(&self.graph) {
            to_visit.push(parent_index);
        }
        for parent_index in to_visit {
            self.visit_node(seen_nodes, &parent_index, dep_order);
        }

        dep_order.push(self.graph[*node].clone());
        // let children = self.graph.children(*node);
        // let mut to_visit = vec![];
        // for (_, child_index) in children.iter(&self.graph) {
        // to_visit.push(child_index);
        // }
        // for child_index in to_visit {
        // self.visit_node(seen_nodes, &child_index, dep_order);
        // }
        //
    }

    // pub fn parents_of_named(&mut self, name: &String) -> Vec<String> {
    // let parents = self.graph.parents(self.node_bucket[name]);
    // let mut retval = vec![];
    // for (parent, parent_index) in parents.iter(&self.graph) {
    // retval.push(parent);
    // }
    // retval
    // }
    //
    pub fn required_parents_of_named(&self, name: &K) -> Vec<&K> {
        let parents = self.graph.parents(self.node_bucket[name]);
        let mut retval = vec![];
        for (edge, node) in parents.iter(&self.graph) {
            if *(self.graph.edge_weight(edge).unwrap()) != DepEdge::Requires {
                continue;
            }
            retval.push(self.graph.node_weight(node).unwrap());
        }
        retval
    }

    pub fn mark_successful(&mut self, dep: &K) {
        self.results.insert(dep.clone(), true);
    }

    pub fn mark_failure(&mut self, dep: &K) {
        self.results.insert(dep.clone(), false);
    }

    pub fn reset_results(&mut self) {
        self.results.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    struct SimpleDep {
        name: String,
        requirements: Vec<String>,
        suggestions: Vec<String>,
        provides: Vec<String>,
    }
    impl SimpleDep {
        pub fn new(name: &str,
                   requirements: Vec<String>,
                   suggestions: Vec<String>,
                   provides: Vec<String>)
                   -> SimpleDep {
            SimpleDep {
                name: name.to_owned(),
                requirements: requirements,
                suggestions: suggestions,
                provides: provides,
            }
        }
    }
    impl Dependency<String> for SimpleDep {
        fn name(&self) -> &String {
            &self.name
        }
        fn requirements(&self) -> &Vec<String> {
            &self.requirements
        }
        fn suggestions(&self) -> &Vec<String> {
            &self.suggestions
        }
        fn provides(&self) -> &Vec<String> {
            &self.provides
        }
    }
    #[test]
    fn single_dep() {
        let mut depgraph = Dependy::new();
        let d1 = SimpleDep::new("single", vec![], vec![], vec![]);
        depgraph.add_dependency(&d1);

        let dep_chain = depgraph.resolve_dependencies(vec![d1]).unwrap();
        assert_eq!(dep_chain.len(), 1);
        assert_eq!(dep_chain[0], "single");
    }

    #[test]
    fn two_deps() {
        let mut depgraph = Dependy::new();
        let d1 = SimpleDep::new("first", vec!["second".to_string()], vec![], vec![]);
        let d2 = SimpleDep::new("second", vec![], vec![], vec![]);
        depgraph.add_dependency(&d1);
        depgraph.add_dependency(&d2);

        let dep_chain = depgraph.resolve_dependencies(vec![d1]).unwrap();
        assert_eq!(dep_chain.len(), 2);
        assert_eq!(dep_chain[0], "second");
        assert_eq!(dep_chain[1], "first");
    }

    #[test]
    fn three_deps() {
        let mut depgraph = Dependy::new();
        let d1 = SimpleDep::new("first", vec!["second".to_string()], vec![], vec![]);
        let d2 = SimpleDep::new("second", vec!["third".to_string()], vec![], vec![]);
        let d3 = SimpleDep::new("third", vec![], vec![], vec![]);
        depgraph.add_dependency(&d1);
        depgraph.add_dependency(&d2);
        depgraph.add_dependency(&d3);

        let dep_chain = depgraph.resolve_dependencies(vec![d1]).unwrap();
        assert_eq!(dep_chain.len(), 3);
        assert_eq!(dep_chain[0], "third");
        assert_eq!(dep_chain[1], "second");
        assert_eq!(dep_chain[2], "first");
    }

    #[test]
    fn provides() {
        let mut depgraph = Dependy::new();
        let d1 = SimpleDep::new("first", vec!["deux".to_string()], vec![], vec![]);
        let d2 = SimpleDep::new("second", vec![], vec![], vec!["deux".to_string()]);
        depgraph.add_dependency(&d1);
        depgraph.add_dependency(&d2);

        let dep_chain = depgraph.resolve_dependencies(vec![d1]).unwrap();
        assert_eq!(dep_chain.len(), 2);
        assert_eq!(dep_chain[0], "second");
        assert_eq!(dep_chain[1], "first");
    }


    #[test]
    fn follows() {
        let mut depgraph = Dependy::new();
        let d1 = SimpleDep::new("first", vec![], vec![], vec![]);
        let d2 = SimpleDep::new("second", vec![], vec![], vec!["deux".to_string()]);
        let d3 = SimpleDep::new("third", vec![], vec![], vec![]);
        depgraph.add_dependency(&d1);
        depgraph.add_dependency(&d2);
        depgraph.add_dependency(&d3);

        let dep_chain = depgraph.resolve_dependencies(vec![d1, d2, d3]).unwrap();
        assert_eq!(dep_chain.len(), 3);
        assert_eq!(dep_chain[0], "first");
        assert_eq!(dep_chain[1], "second");
        assert_eq!(dep_chain[2], "third");
    }

    #[test]
    fn depends_and_follows() {
        let mut depgraph = Dependy::new();
        let d1 = SimpleDep::new("first", vec!["third".to_string()], vec![], vec![]);
        let d2 = SimpleDep::new("second", vec![], vec![], vec!["deux".to_string()]);
        let d3 = SimpleDep::new("third", vec![], vec![], vec![]);
        depgraph.add_dependency(&d1);
        depgraph.add_dependency(&d2);
        depgraph.add_dependency(&d3);

        let dep_chain = depgraph.resolve_dependencies(vec![d1, d3, d2]).unwrap();
        assert_eq!(dep_chain.len(), 3);
        assert_eq!(dep_chain[0], "third");
        assert_eq!(dep_chain[1], "first");
        assert_eq!(dep_chain[2], "second");
    }

    #[test]
    fn complex_sequence() {
        let mut depgraph = Dependy::new();
        let build_ltc_os = SimpleDep::new("build-ltc-os",
                                          vec!["checkout-ltc-os".to_string()],
                                          vec![],
                                          vec![]);
        depgraph.add_dependency(&build_ltc_os);
        let checkout_ltc_os = SimpleDep::new("checkout-ltc-os", vec![], vec![], vec![]);
        depgraph.add_dependency(&checkout_ltc_os);
        let connectivity_test = SimpleDep::new("connectivity-test",
                                               vec!["serial-test".to_string()],
                                               vec![],
                                               vec![]);
        depgraph.add_dependency(&connectivity_test);
        let finish_ltc_tests = SimpleDep::new("finish-ltc-tests",
                                              vec!["serial-test".to_string(),
                                                   "connectivity-test".to_string(),
                                                   "led-test".to_string(),
                                                   "rgb-test".to_string(),
                                                   "status-leds".to_string()],
                                              vec![],
                                              vec![]);
        depgraph.add_dependency(&finish_ltc_tests);
        let led_test = SimpleDep::new("led-test", vec!["serial-test".to_string()], vec![], vec![]);
        depgraph.add_dependency(&led_test);
        let mass_erase = SimpleDep::new("mass-erase", vec!["swd".to_string()], vec![], vec![]);
        depgraph.add_dependency(&mass_erase);
        let measure_reset_pulse = SimpleDep::new("measure-reset-pulse",
                                                 vec!["pi-blaster".to_string()],
                                                 vec![],
                                                 vec![]);
        depgraph.add_dependency(&measure_reset_pulse);
        let pi_blaster = SimpleDep::new("pi-blaster", vec![], vec![], vec![]);
        depgraph.add_dependency(&pi_blaster);
        let program_app = SimpleDep::new("program-app",
                                         vec!["finish-ltc-tests".to_string()],
                                         vec![],
                                         vec![]);
        depgraph.add_dependency(&program_app);
        let program_os_pvt1c = SimpleDep::new("program-os-pvt1c",
                                              vec!["swd".to_string(), "mass-erase".to_string()],
                                              vec![],
                                              vec![]);
        depgraph.add_dependency(&program_os_pvt1c);
        let rgb_test = SimpleDep::new("rgb-test", vec!["serial-test".to_string()], vec![], vec![]);
        depgraph.add_dependency(&rgb_test);
        let serial_test = SimpleDep::new("serial-test",
                                         vec!["upload-program".to_string()],
                                         vec![],
                                         vec![]);
        depgraph.add_dependency(&serial_test);
        let status_leds = SimpleDep::new("status-leds",
                                         vec!["serial-test".to_string()],
                                         vec![],
                                         vec![]);
        depgraph.add_dependency(&status_leds);
        let swd = SimpleDep::new("swd",
                                 vec!["measure-reset-pulse".to_string()],
                                 vec![],
                                 vec![]);
        depgraph.add_dependency(&swd);
        let test_setup = SimpleDep::new("test-setup",
                                        vec!["program-os-pvt1c".to_string()],
                                        vec![],
                                        vec![]);
        depgraph.add_dependency(&test_setup);
        let upload_program = SimpleDep::new("upload-program",
                                            vec!["program-os-pvt1c".to_string(),
                                                 "test-setup".to_string()],
                                            vec![],
                                            vec![]);
        depgraph.add_dependency(&upload_program);
        let wait_forever = SimpleDep::new("wait-forever", vec![], vec![], vec![]);
        depgraph.add_dependency(&wait_forever);

        let dep_chain = depgraph.resolve_dependencies(vec![mass_erase,
                                       program_os_pvt1c,
                                       upload_program,
                                       finish_ltc_tests,
                                       program_app])
            .unwrap();

        {
            let mut dotfile = File::create("./depgraph.dot").expect("Unable to open depgraph.dot");
            depgraph.save_dot(&mut dotfile).expect("Unable to write dotfile");
        }

        println!("Resolved dep chain: {:?}", dep_chain);
        for depname in &dep_chain {
            validate_parents_present(&depgraph, &dep_chain, &depname);
        }
    }

    fn index_of(vector: &Vec<String>, x: &String) -> Option<usize> {
        for (idx, val) in vector.iter().enumerate() {
            if val == x {
                return Some(idx);
            }
        }
        return None;
    }

    fn validate_parents_present(depgraph: &Dependy<String>,
                                dep_chain: &Vec<String>,
                                depname: &String)
                                -> bool {
        // Get the next item from the depgraph.  It _must_ exist.
        let item = depgraph.dep_map.get(depname).unwrap();
        let my_index = index_of(dep_chain, depname).unwrap();
        for req in item.requirements() {
            assert!(dep_chain.contains(req));

            let their_index = index_of(dep_chain, req).unwrap();
            assert!(their_index < my_index);

            // Validate that the requirement has all elements present.
            validate_parents_present(depgraph, dep_chain, req);
        }

        for req in item.suggestions() {
            assert!(dep_chain.contains(req));

            // Validate that the requirement has all elements present.
            validate_parents_present(depgraph, dep_chain, req);
        }
        true
    }
}
