extern crate daggy;

use self::daggy::{Dag, Walker, NodeIndex};

use std::collections::HashMap;

pub enum DepError {
    RequirementsNotFound(String),
    RequirementNotFound(String, String),
    SuggestionsNotFound(String),
    SuggestionNotFound(String, String),
    CircularDependency(String, String),
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum TestEdge {
    /// Test B Requires test A, and a failure of A prevents B from running
    Requires,

    /// Test B Suggests test A, and a failure of A doesn't prevent B from running
    Suggests,

    /// Test B follows test A in the .scenario file
    Follows,
}

pub trait Dependency {
    fn name(&self) -> &String;
    fn requirements(&self) -> &Vec<String>;
    fn suggestions(&self) -> &Vec<String>;
    fn provides(&self) -> &Vec<String>;
}

pub struct Dependable {
    /// The graph structure, which we will iterate over.
    graph: Dag<String, TestEdge>,

    /// A hashmap containing all nodes in the graph, indexed by name.
    node_bucket: HashMap<String, NodeIndex>,

    /// Whether results were successful or not.
    results: HashMap<bool, String>,

    requirements: HashMap<String, Vec<String>>,
    suggestions: HashMap<String, Vec<String>>,
}

impl Dependable {
    pub fn new() -> Dependable {
        Dependable {
            graph: Dag::new(),
            node_bucket: HashMap::new(),
            results: HashMap::new(),
            requirements: HashMap::new(),
            suggestions: HashMap::new(),
        }
    }

    pub fn add_dependency<T: Dependency>(&mut self, dependency: T) {
        let name = dependency.name();
        let new_node = self.graph.add_node(name.clone());
        self.node_bucket.insert(name.clone(), new_node.clone());

        // Also add aliases
        for alias in dependency.provides() {
            self.node_bucket.insert(alias.clone(), new_node.clone());
        }

        self.suggestions.insert(name.clone(), dependency.suggestions().clone());
        self.requirements.insert(name.clone(), dependency.requirements().clone());
    }

    pub fn resolve_dependencies<T: Dependency>(&mut self,
                                               dependencies: Vec<T>)
                                               -> Result<Vec<String>, DepError> {

        let mut to_resolve = vec![];
        for dep in dependencies {
            to_resolve.push(dep.name().clone());
        }

        let mut resolved = HashMap::new();

        loop {
            if to_resolve.is_empty() {
                break;
            }

            // If this dep_name has been resolved, skip it.
            let dep_name = to_resolve.remove(0);
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
                            None => return Err(DepError::RequirementNotFound(dep_name, req.clone())),
                            Some(e) => e,
                        };

                        if let Err(_) = self.graph
                            .add_edge(*edge, self.node_bucket[&dep_name], TestEdge::Requires) {
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
                            .add_edge(*edge, self.node_bucket[&dep_name], TestEdge::Requires) {
                            return Err(DepError::CircularDependency(dep_name.clone(), req.clone()));
                        }
                    }
                }
            }
        }

        // Add "Follows" dependencies, if no other dependency exists.

        Ok(vec![])
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {}
}
