extern crate conch_parser;

use conch_parser::token::Positional;

#[test]
fn test_positional_conversions() {
    for i in 0..10u8 {
        let positional = Positional::from_num(i).expect(&format!("failed to convert {}", i));
        assert_eq!(positional.as_num(), i);
    }

    assert_eq!(Positional::from_num(10), None);
}
