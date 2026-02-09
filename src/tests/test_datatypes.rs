// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#[cfg(test)]
mod test_datatypes {
    use crate::datatypes::{extract_datatype_info, print_datatype_summary};
    use yaspar_ir::ast::{Context, Typecheck};
    use yaspar_ir::untyped::UntypedAst;

    #[test]
    fn test_extract_datatype_info() {
        // Test SMT input with datatype declarations
        let smt_input = r#"
(declare-datatypes () ((List (nil) (cons (head Int) (tail List)))))
(declare-datatypes () ((Tree (leaf (value Int)) (node (left Tree) (right Tree)))))
"#;

        // Parse and type-check the input
        let commands = UntypedAst.parse_script_str(smt_input).unwrap();
        let mut context = Context::new();
        
        for cmd in commands {
            cmd.type_check(&mut context).unwrap();
        }

        // Extract datatype information
        let datatype_info = extract_datatype_info(&context);
        
        // Verify we found the expected datatypes
        assert_eq!(datatype_info.sorts.len(), 2);
        
        // Check for List datatype
        let list_sort = datatype_info.sorts.iter().find(|s| s.name == "List");
        assert!(list_sort.is_some());
        assert_eq!(list_sort.unwrap().params.len(), 0);
        
        // Check for Tree datatype
        let tree_sort = datatype_info.sorts.iter().find(|s| s.name == "Tree");
        assert!(tree_sort.is_some());
        assert_eq!(tree_sort.unwrap().params.len(), 0);
        
        // Verify we found constructors
        assert!(datatype_info.constructors.len() >= 4); // nil, cons, leaf, node
        
        // Check specific constructors
        let nil_ctor = datatype_info.constructors.iter().find(|c| c.name == "nil");
        assert!(nil_ctor.is_some());
        assert_eq!(nil_ctor.unwrap().datatype, "List");
        assert_eq!(nil_ctor.unwrap().field_names.len(), 0);
        
        let cons_ctor = datatype_info.constructors.iter().find(|c| c.name == "cons");
        assert!(cons_ctor.is_some());
        assert_eq!(cons_ctor.unwrap().datatype, "List");
        assert_eq!(cons_ctor.unwrap().field_names.len(), 2);
        assert!(cons_ctor.unwrap().field_names.contains(&"head".to_string()));
        assert!(cons_ctor.unwrap().field_names.contains(&"tail".to_string()));
        
        println!("Datatype extraction test passed!");
        print_datatype_summary(&datatype_info);
    }
    
    #[test] 
    fn test_empty_context() {
        let context = Context::new();
        let datatype_info = extract_datatype_info(&context);
        
        // Empty context should have no datatypes
        assert_eq!(datatype_info.sorts.len(), 0);
        assert_eq!(datatype_info.constructors.len(), 0);
        assert_eq!(datatype_info.selectors.len(), 0);
        assert_eq!(datatype_info.testers.len(), 0);
        assert_eq!(datatype_info.terms.len(), 0);
        
        println!("Empty context test passed!");
    }
}
