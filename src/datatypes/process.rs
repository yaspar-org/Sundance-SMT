use yaspar_ir::ast::alg::DatatypeDec;
use yaspar_ir::ast::{Context, Sig, Sort, SortDef, Str};

use crate::utils::{DeterministicHashMap, DeterministicHashSet};
// use std::collections::DeterministicHashSet;

#[derive(Debug, Clone)]
pub struct DatatypeInfo {
    pub sorts: DeterministicHashMap<String, DatatypeSort>,
    pub constructors: DeterministicHashMap<String, DatatypeConstructor>,
}

#[derive(Debug, Clone, PartialEq, PartialOrd, Eq, Ord)]
pub struct DatatypeSort {
    pub name: String,
    pub params: Vec<String>,
}

#[derive(Debug, Clone)]
pub struct DatatypeConstructor {
    pub datatype: String,
    pub datatype_sort: Sort,
    pub field_names: Vec<String>,
    pub field_sorts: Vec<Sort>,
}

impl DatatypeInfo {
    pub fn new() -> Self {
        Self {
            sorts: DeterministicHashMap::new(),
            constructors: DeterministicHashMap::new(),
        }
    }
}

impl Default for DatatypeInfo {
    fn default() -> Self {
        Self::new()
    }
}

/// Extract all datatype-related information from the given context.
///
/// This function analyzes the context and collects:
/// - All datatype sorts with their parameters
/// - All constructors with their field information  
/// - All selectors (field accessors)
/// - All testers ((_ is Constructor) predicates)
/// - All terms that have a datatype type
pub fn extract_datatype_info(context: &Context) -> DatatypeInfo {
    let mut info = DatatypeInfo::new();
    let mut datatype_names = DeterministicHashSet::new();

    // First pass: collect all datatype sorts
    extract_datatype_sorts(context, &mut info, &mut datatype_names);

    info
}

/// Extract all datatype sorts from the context
fn extract_datatype_sorts(
    context: &Context,
    info: &mut DatatypeInfo,
    datatype_names: &mut DeterministicHashSet<String>,
) {
    let sorts = context.expose_sorts();

    for (sort_name, sort_def) in sorts {
        if let SortDef::Datatype(datatype_dec) = sort_def {
            let name = get_string_from_str(sort_name);
            datatype_names.insert(name.clone());

            let params = datatype_dec
                .params
                .iter()
                .map(get_string_from_str)
                .collect();

            info.sorts.insert(
                name.clone(),
                DatatypeSort {
                    name: name.clone(),
                    params,
                },
            );

            // Extract constructors from this datatype
            extract_constructors_from_datatype(context, &name, datatype_dec, info);
        }
    }
}

/// Extract constructors from a single datatype declaration
fn extract_constructors_from_datatype(
    context: &Context,
    datatype_name: &str,
    // datatype_sort: &SortDef ,
    datatype_dec: &DatatypeDec<Str, Sort>,
    info: &mut DatatypeInfo,
) {
    for constructor in &datatype_dec.constructors {
        let ctor_name = get_string_from_str(&constructor.ctor);
        let mut field_names = Vec::new();
        let mut field_sorts = Vec::new();

        for arg in &constructor.args {
            field_names.push(get_string_from_str(&arg.0));
            field_sorts.push(arg.2.clone());
        }

        // todo: doing this to get the return sort of a constructor, but there's hopefully a nicer way to do it
        let sig_list = context
            .expose_symbol_table()
            .get(&constructor.ctor)
            .unwrap();
        assert!(sig_list.len() == 1);
        let (sig, _) = sig_list[0].clone();
        let sort = if let Sig::ParFunc(_, _, _, sort) = sig {
            sort
        } else {
            panic!("constructor should be a function")
        };

        info.constructors.insert(
            ctor_name,
            DatatypeConstructor {
                // name: ctor_name,
                datatype: datatype_name.to_string(),
                datatype_sort: sort,
                field_names: field_names.clone(),
                field_sorts,
            },
        );

        // actually don't think I need to do selectors for right now because I never need to look up based on selectors
        // for name in field_names {
        //     info.selectors.insert(name, DatatypeSelector { constructor: (), datatype: (), field_sort: () })
        // }
    }
}

/// Convert a Str to String (helper function)
fn get_string_from_str(str_val: &Str) -> String {
    // This assumes Str has a way to get the underlying string
    // The actual implementation may vary depending on the Str type
    format!("{}", str_val)
}

// /// Check if there are any inductive datatypes in the context and panic if found
// ///
// /// An inductive datatype is one that references itself (directly or indirectly)
// /// in its constructor fields. For example:
// /// - List with constructor cons(head: Int, tail: List)
// /// - Tree with constructor node(left: Tree, right: Tree)
pub fn check_for_inductive_datatypes_and_panic(context: &Context) -> DatatypeInfo {
    let datatype_info = extract_datatype_info(context);

    for sort_name in datatype_info.sorts.keys() {
        if is_inductive_datatype(sort_name, &datatype_info) {
            panic!(
                "Found inductive datatype: {}. Inductive datatypes are not supported!",
                sort_name
            );
        }
    }

    datatype_info
}

// /// Check if a specific datatype is inductive by examining its constructors
fn is_inductive_datatype(datatype_name: &str, info: &DatatypeInfo) -> bool {
    // A datatype is inductive if any of its constructors have fields that reference the datatype itself
    for constructor in info.constructors.values() {
        if constructor.datatype == datatype_name {
            // Check if any field of this constructor references the same datatype
            for field_sort in &constructor.field_sorts {
                if field_sort.to_string() == datatype_name {
                    return true;
                }

                // Also check for indirect references (though this is a simplified check)
                // For more complex mutual recursion detection, we'd need a more sophisticated algorithm
                if is_mutually_recursive(
                    field_sort,
                    datatype_name,
                    info,
                    &mut DeterministicHashSet::new(),
                ) {
                    return true;
                }
            }
        }
    }
    false
}

// /// Check for mutual recursion between datatypes (simplified version)
fn is_mutually_recursive(
    field_sort: &Sort,
    target_datatype: &str,
    info: &DatatypeInfo,
    visited: &mut DeterministicHashSet<Sort>,
) -> bool {
    // Avoid infinite recursion in checking
    if visited.contains(field_sort) {
        return false;
    }
    visited.insert(field_sort.clone());

    // If the field sort is not a datatype we know about, it's not recursive
    let is_known_datatype = info
        .sorts
        .iter()
        .any(|(name, _)| *name == field_sort.to_string());
    if !is_known_datatype {
        return false;
    }

    // Check if this field_sort's constructors eventually lead back to target_datatype
    for constructor in info.constructors.values() {
        if constructor.datatype == field_sort.to_string() {
            for nested_field_sort in &constructor.field_sorts {
                if nested_field_sort.to_string() == target_datatype {
                    return true;
                }
                if is_mutually_recursive(nested_field_sort, target_datatype, info, visited) {
                    return true;
                }
            }
        }
    }

    false
}
