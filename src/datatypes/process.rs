// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use std::collections::HashSet;
use yaspar_ir::ast::{Context, DatatypeDec, Sort, SortDef, Str};

use crate::utils::DeterministicHashMap;

#[derive(Debug, Clone)]
pub struct DatatypeInfo {
    /// Map datatype names to their datatype definitions
    pub datatypes: DeterministicHashMap<Str, DatatypeDec>,
    /// Map constructor names to their datatypes
    pub constructors: DeterministicHashMap<Str, Str>,
}

impl DatatypeInfo {
    pub fn new() -> Self {
        Self {
            datatypes: Default::default(),
            constructors: Default::default(),
        }
    }

    pub fn is_datatype(&self, sort: &Str) -> bool {
        self.datatypes.contains_key(sort)
    }
}

impl Default for DatatypeInfo {
    fn default() -> Self {
        Self::new()
    }
}

impl DatatypeInfo {
    pub fn from_context(context: &Context) -> Self {
        // we first collect all the names for datatypes
        let mut datatypes: DeterministicHashMap<_, _> = Default::default();
        let mut constructors: DeterministicHashMap<_, _> = Default::default();
        for k in context.all_sorts() {
            if let Some(SortDef::Datatype(dt)) = context.get_sort_def(k) {
                for ctor in &dt.constructors {
                    constructors.insert(ctor.ctor.clone(), k.clone());
                }
                datatypes.insert(k.clone(), dt.clone());
            }
        }

        Self {
            datatypes,
            constructors,
        }
    }

    /// Return the name of a recursive datatype if one exists
    pub fn contains_recursive_datatype(&self, context: &Context) -> Option<Str> {
        let mut visiting = Default::default();
        for name in self.datatypes.keys() {
            if check_is_recursive_datatype(context, name, &mut visiting) {
                return Some(name.clone());
            }
        }
        None
    }
}

/// determine whether a sort contains a recursive datatype
fn check_sort_contains_recursive_datatype(
    context: &Context,
    sort: &Sort,
    visiting: &mut HashSet<Str>,
) -> bool {
    check_is_recursive_datatype(context, sort.sort_name(), visiting)
    // we do not need to look into sort.1 because we know datatype recursion can only occur as the
    // top symbol as per the standard.
}

/// Check whether a given name refers to a recursive datatype
fn check_is_recursive_datatype(context: &Context, name: &Str, visiting: &mut HashSet<Str>) -> bool {
    if visiting.contains(name) {
        visiting.remove(name);
        return true;
    }
    visiting.insert(name.clone());

    if let Some(SortDef::Datatype(dt)) = context.get_sort_def(name) {
        let recursive = dt.constructors.iter().any(|ctor| {
            ctor.args
                .iter()
                .any(|arg| check_sort_contains_recursive_datatype(context, &arg.2, visiting))
        });
        visiting.remove(name);
        return recursive;
    }
    visiting.remove(name);
    false
}

#[cfg(test)]
mod tests {
    use super::*;
    use yaspar_ir::ast::{StrAllocator, Typecheck};
    use yaspar_ir::untyped::UntypedAst;

    #[test]
    fn test_recursive_test() {
        let smt_input = r#"
            (declare-datatypes ((Option 1)) ((par (T) ((None) (Some (value T))))))
        "#;
        let cmd = UntypedAst.parse_command_str(smt_input).unwrap();
        let mut context = Context::default();
        context.ensure_logic();
        cmd.type_check(&mut context).unwrap();
        let dt_info = DatatypeInfo::from_context(&context);
        assert!(dt_info.contains_recursive_datatype(&context).is_none());

        let smt_input2 = r#"
            (declare-datatypes ((List 1)) ((par (T) ((Nil) (Cons (head T) (tail (List T)))))))
        "#;
        let cmd2 = UntypedAst.parse_command_str(smt_input2).unwrap();
        cmd2.type_check(&mut context).unwrap();
        let dt_info2 = DatatypeInfo::from_context(&context);
        let list_sym = context.allocate_symbol("List");
        assert_eq!(
            dt_info2.contains_recursive_datatype(&context),
            Some(list_sym)
        );
    }
}
