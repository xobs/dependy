extern crate daggy;

use self::daggy::{Dag, Walker, NodeIndex};

use std::collections::HashMap;

#[derive(Debug)]
pub enum DepError {
    RequirementsNotFound(String),
    RequirementNotFound(String, String),
    SuggestionsNotFound(String),
    SuggestionNotFound(String, String),
    DependencyNotFound(String),
    CircularDependency(String, String),
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

pub trait Dependency {
    fn name(&self) -> &str;
    fn requirements(&self) -> &Vec<String>;
    fn suggestions(&self) -> &Vec<String>;
    fn provides(&self) -> &Vec<String>;
}

#[derive(Debug)]
pub struct Dependy {
    /// The graph structure, which we will iterate over.
    graph: Dag<String, DepEdge>,

    /// A hashmap containing all nodes in the graph, indexed by name.
    node_bucket: HashMap<String, NodeIndex>,

    /// Whether results were successful or not.
    results: HashMap<String, bool>,

    /// A mapping of "provides" to actual names.
    provides_map: HashMap<String, String>,

    requirements: HashMap<String, Vec<String>>,
    suggestions: HashMap<String, Vec<String>>,
}

impl Dependy {
    pub fn new() -> Dependy {
        Dependy {
            graph: Dag::new(),
            node_bucket: HashMap::new(),
            results: HashMap::new(),
            requirements: HashMap::new(),
            suggestions: HashMap::new(),
            provides_map: HashMap::new(),
        }
    }

    pub fn add_dependency<T: Dependency>(&mut self, dependency: &T) {
        let name = dependency.name().to_string();
        let new_node = self.graph.add_node(name.clone());
        self.node_bucket.insert(name.clone(), new_node.clone());

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
                                      dependencies: &Vec<String>)
                                      -> Result<Vec<String>, DepError> {

        let mut to_resolve = dependencies.clone();
        let mut resolved = HashMap::new();

        loop {
            if to_resolve.is_empty() {
                break;
            }

            // If this dep_name has been resolved, skip it.
            let dep_name = to_resolve.remove(0);
            let dep_name = match self.provides_map.get(&dep_name) {
                Some(s) => s.clone(),
                None => return Err(DepError::DependencyNotFound(dep_name)),
            };
            if resolved.get(&dep_name).is_some() {
                continue;
            }
            resolved.insert(dep_name.clone(), ());

            // Resolve all requirements.
            match self.requirements.get(&dep_name) {
                None => return Err(DepError::RequirementsNotFound(dep_name.clone())),
                Some(ref reqs) => {
                    for req in *reqs {
                        to_resolve.push(req.clone());
                        let edge = match self.node_bucket.get(req) {
                            None => {
                                return Err(DepError::RequirementNotFound(dep_name, req.clone()))
                            }
                            Some(e) => e,
                        };

                        if let Err(_) = self.graph
                            .add_edge(*edge, self.node_bucket[&dep_name], DepEdge::Requires) {
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
                        let edge = match self.node_bucket.get(req) {
                            None => return Err(DepError::SuggestionNotFound(dep_name, req.clone())),
                            Some(e) => e,
                        };

                        if let Err(_) = self.graph
                            .add_edge(*edge, self.node_bucket[&dep_name], DepEdge::Requires) {
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
            // If we get a "CircularDependency", that's fine, we just won't add this edge.
            self.graph.add_edge(*previous_edge, *this_edge, DepEdge::Follows).ok();
        }

        // Sort everything into a "dependency order"
        let mut dep_order = vec![];
        {
            let mut seen_nodes = HashMap::new();
            // Pick a node from the bucket and visit it.  This will cause
            // all nodes in the graph to be visited, in order.
            let some_node = self.node_bucket.get(&dependencies[0]).unwrap().clone();
            self.visit_node(&mut seen_nodes, &some_node, &mut dep_order);
        }
        Ok(dep_order)
    }

    pub fn resolve_dependencies<T: Dependency>(&mut self,
                                               dependencies: Vec<T>)
                                               -> Result<Vec<String>, DepError> {
        let mut to_resolve = vec![];
        for dep in &dependencies {
            to_resolve.push(dep.name().to_string());
        }
        self.resolve_named_dependencies(&to_resolve)
    }

    fn visit_node(&mut self,
                  seen_nodes: &mut HashMap<NodeIndex, ()>,
                  node: &NodeIndex,
                  dep_order: &mut Vec<String>) {

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

        let children = self.graph.children(*node);
        let mut to_visit = vec![];
        for (_, child_index) in children.iter(&self.graph) {
            to_visit.push(child_index);
        }
        for child_index in to_visit {
            self.visit_node(seen_nodes, &child_index, dep_order);
        }
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
    pub fn required_parents_of_named(&self, name: &String) -> Vec<&String> {
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

    pub fn mark_successful(&mut self, dep: &String) {
        self.results.insert(dep.clone(), true);
    }

    pub fn mark_failure(&mut self, dep: &String) {
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
                name: name.to_string(),
                requirements: requirements,
                suggestions: suggestions,
                provides: provides,
            }
        }
    }
    impl Dependency for SimpleDep {
        fn name(&self) -> &str {
            &self.name.as_str()
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
        assert_eq!(dep_chain[1], "second");
        assert_eq!(dep_chain[2], "first");
    }
}
