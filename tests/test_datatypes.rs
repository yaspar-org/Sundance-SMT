// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

// This file tests the datatype processing functionality
// Since this is a binary crate without lib.rs, we need to include the modules directly

// Include the module path - this will be replaced with proper imports when lib.rs exists
use yaspar_ir::ast::{Context, StrAllocator, Typecheck};
use yaspar_ir::untyped::UntypedAst;

#[test]
fn test_datatype_parsing_and_typechecking() {
    // Test SMT input with datatype declarations - try simpler syntax
    let smt_input = r#"
(declare-datatype List ((nil) (cons (head Int) (tail List))))
(declare-datatype Tree ((leaf (value Int)) (node (left Tree) (right Tree))))
"#;

    // Parse and type-check the input
    let commands = UntypedAst.parse_script_str(smt_input).unwrap();
    let mut context = Context::new();

    for cmd in commands {
        cmd.type_check(&mut context).unwrap();
    }

    // Check that List and Tree sorts exist (allocate symbols first)
    let list_name = context.allocate_symbol("List");
    let tree_name = context.allocate_symbol("Tree");

    // Verify that the context now knows about the datatypes
    let sorts = context.expose_sorts();

    // Should have at least our two datatypes
    assert!(sorts.len() >= 2);

    assert!(sorts.contains_key(&list_name));
    assert!(sorts.contains_key(&tree_name));

    println!("Datatype parsing and type checking test passed!");
}
