// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Context tracked during SMT to [crate::arithmetic::lia::linear_system::LinearSystem] conversion

use std::collections::HashMap;

use dashu::Rational;

use crate::arithmetic::lia::linear_system::Rel;
use crate::arithmetic::lia::variables::{Var, VarType};
use yaspar_ir::ast::{self, Sort};

/// Context used during conversion from Linear relation ASTs to `LinExpr`
///
/// During conversion, we have [ast::Term]s converted to [Rel]ations and unique (slack) [Var]iables.
///
/// ```text
/// t_i -> r_i
///     -> slack_i (become basic variables in the tableau)
///```
///
/// To build a [crate::arithmetic::lia::lra_solver::LRASolver], we need to know the association `r_i -> slack_i` and keep
/// the relations and slack/basic variables in a fixed order. This is best done by
/// keeping a pair of vectors `(Vec<Rel>, Var<Var>)` since we only need to iterate over
/// them in the fixed order.
///
/// After solving, we have return data. Either:
///
/// ```text
/// FEASIBLE(Var -> Rational)
/// INFEASIBLE({Var}) (where all Var are basic variables)
/// ```
///
/// These need to be converted to:
///
/// ```text
/// FEASIBLE(Term -> Rational) (where only term variables are keys)
/// INFEASIBLE({Terms}) (where all Terms are input arithmetic literals)
/// ```
///
/// Need to track associations:
///
/// ```text
/// Var -> Term
///```
#[derive(Clone, Debug)]
pub struct ConvContext {
    /// next fresh unique id
    next_id: usize,

    /// mapping: variable name -> Var
    name_to_var: HashMap<String, Var>,
    /// reverse mapping: Var -> variable name
    var_to_name: HashMap<Var, String>,

    /// mapping: Input [ast::Term] (could be a variable or a linear expression term) -> Var
    term_to_var: HashMap<ast::Term, Var>,
    /// mapping: Var -> Input [ast::Term]
    var_to_term: HashMap<Var, ast::Term>,

    /// List of relations, in the fixed order that they are added to the context
    relations: Vec<Rel<Rational>>,
    /// List of (slack) variables corresponding to relations in `self.relations`
    relation_vars: Vec<Var>,
}

impl ConvContext {
    /// Create a new conversion context with new empty id mappings and fresh id 0
    pub fn new() -> Self {
        ConvContext {
            next_id: 0,
            name_to_var: HashMap::new(),
            var_to_name: HashMap::new(),
            term_to_var: HashMap::new(),
            var_to_term: HashMap::new(),
            relations: Vec::new(),
            relation_vars: Vec::new(),
        }
    }

    /// Return contained (relation, variable) pairs in the order they were added to the context
    pub fn get_relations(&self) -> impl Iterator<Item = (&Rel<Rational>, &Var)> {
        self.relations.iter().zip(self.relation_vars.iter())
    }

    /// Return contained (relation, variable) pairs in the order they were added to the context
    pub fn get_relations_mut(&mut self) -> impl Iterator<Item = (&mut Rel<Rational>, &mut Var)> {
        self.relations.iter_mut().zip(self.relation_vars.iter_mut())
    }

    /// Return the number of contained relations
    pub fn num_relations(&self) -> usize {
        self.relations.len()
    }

    /// Filter associated variables and relations based on a variable predicate
    ///
    /// Filtering preserves the order of relations/vars.
    pub fn filter_vars<P>(&mut self, pred: P)
    where
        P: Fn(&Var) -> bool,
    {
        // TODO: filter_vars: find a better solution to var/relation filtering
        let mut new_relations = Vec::new();
        let mut new_relation_vars = Vec::new();
        for (i, v) in self.relation_vars.iter().enumerate() {
            if pred(v) {
                new_relation_vars.push(*v);
                new_relations.push(self.relations[i].clone()); // TODO: don't clone
            }
        }
        self.relations = new_relations;
        self.relation_vars = new_relation_vars;
    }

    /// Allocate a new variable based on name and variable <-> name association.
    ///
    /// Return the existing variable if one has already been allocated by name.
    pub fn allocate_var(&mut self, name: &str, typ: VarType) -> Var {
        if let Some(i) = self.get_var(name) {
            return *i;
        }
        let new_var = Var::new(self.next_id, typ);
        self.next_id += 1;
        // TODO: intern the strings instead of copying
        self.name_to_var.insert(name.to_string(), new_var);
        self.var_to_name.insert(new_var, name.to_string());
        new_var
    }

    /// Allocate a new variable based on name and variable <-> name association.
    ///
    /// If a term is given, add a variable <-> term association. Return the existing variable if
    /// one has already been allocated by name.
    ///
    /// TODO: allocate_var_term: consolidate the 3 allocation methods
    pub fn allocate_var_term(&mut self, name: &str, typ: VarType, term: ast::Term) -> Var {
        if let Some(i) = self.get_var(name) {
            return *i;
        }
        let new_var = Var::new(self.next_id, typ);
        self.next_id += 1;
        // TODO: intern the strings instead of copying
        self.name_to_var.insert(name.to_string(), new_var);
        self.var_to_name.insert(new_var, name.to_string());
        self.term_to_var.insert(term.clone(), new_var);
        self.var_to_term.insert(new_var, term);
        new_var
    }

    /// Allocate a new variable, with auto-generated name, representing a term; if an associated variable has already been
    /// allocated, return it.
    ///
    /// Note: [ast::Term] is cheap to copy; it is hconsed and holds an id and a ref
    pub fn allocate_term(
        &mut self,
        term: ast::Term,
        maybe_name: Option<&str>,
        var_type: Option<Sort>,
    ) -> Var {
        if let Some(v) = self.get_term(term.clone()) {
            return v;
        }
        let new_id = self.next_id;
        let new_var_name = maybe_name
            .map(|s| s.to_string())
            .unwrap_or(format!("$lit_{new_id}"));
        let new_var = match var_type {
            Some(hs) => {
                let rsort = hs.get();
                let name = rsort.sort_name().get().as_str();
                let ind = &rsort.1;
                debug_assert!(ind.is_empty()); // expect no sort parameters
                if name == "Real" {
                    Var::real(new_id)
                } else if name == "Int" {
                    Var::int(new_id)
                } else {
                    unreachable!() // unreachable assuming type checking and logic is set correctly
                }
            }
            None => {
                Var::real(new_id) // by default all slack variables have type Real
            }
        };
        self.next_id += 1;
        self.term_to_var.insert(term.clone(), new_var);
        self.var_to_term.insert(new_var, term);
        self.name_to_var.insert(new_var_name.clone(), new_var);
        self.var_to_name.insert(new_var, new_var_name);
        new_var
    }

    /// Add a relation to the context and allocate a (slack) variable associated to it;
    /// return the variable
    pub fn allocate_relation(&mut self, rel: Rel<Rational>) -> Var {
        let mut id = self.next_id;
        let mut name = format!("!slack_{id}");
        while self.name_to_var.contains_key(&name) {
            // only reachable if the input problem contains variables named `!slack_i`
            id += 1;
            name = format!("!slack_{id}");
        }
        // we now have a fresh name, but note the name id is not guaranteed to equal
        // the internal Var id
        let s = self.allocate_var(&name, VarType::Real);
        self.push_relation(rel, s);
        s
    }

    /// Associate a new relation and slack variable in the context.
    ///
    /// The order that relations are pushed in is maintained.
    ///
    /// The association is used primarily in order to report conflicts in terms of the
    /// input terms at the frontend. Internally, conflicts correspond to subsets of
    /// the slack variables / converted linear relations / basic variables.
    pub fn push_relation(&mut self, rel: Rel<Rational>, var: Var) {
        self.relations.push(rel);
        self.relation_vars.push(var);
    }

    /// Get the id associated to a name, if present
    pub fn get_var(&self, name: &str) -> Option<&Var> {
        self.name_to_var.get(name)
    }

    /// Get the id associated to a term, if present
    pub fn get_term(&self, term: ast::Term) -> Option<Var> {
        self.term_to_var.get(&term).copied()
    }

    /// Copy and return all the ids in the context
    pub fn get_all_vars(&self) -> impl Iterator<Item = Var> {
        self.var_to_name.keys().copied()
    }

    #[allow(dead_code)]
    /// Get name associated with an id, if present
    pub fn get_name(&self, var: Var) -> Option<&str> {
        self.var_to_name.get(&var).map(|s| s.as_str())
    }

    /// Return the [ast::Term] <-> [Var] mappings
    pub fn get_term_var_maps(&self) -> (HashMap<ast::Term, Var>, HashMap<Var, ast::Term>) {
        (self.term_to_var.clone(), self.var_to_term.clone())
    }
}

impl Default for ConvContext {
    fn default() -> Self {
        Self::new()
    }
}
