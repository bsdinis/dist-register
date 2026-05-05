use vstd::prelude::*;

verus! {

#[macro_export]
macro_rules! vprint {
    ($($arg:tt)*) => {
        #[cfg(not(verus_only))]
        {
        use $crate::print::*;
        let s = format!($($arg)*);
        print(&s)
    }
        #[cfg(verus_only)]
        {
        }
    };
}

#[macro_export]
macro_rules! veprint {
    ($($arg:tt)*) => {
        #[cfg(not(verus_only))]
        {
        use $crate::print::*;
        let s = format!($($arg)*);
        eprint(&s)
    }
        #[cfg(verus_only)]
        {
        }
    };
}

#[macro_export]
macro_rules! vprintln {
    ($($arg:tt)*) => {
        #[cfg(not(verus_only))]
        {
        use $crate::print::*;
        let s = format!($($arg)*);
        println(&s)
        }
        #[cfg(verus_only)]
        {
        }
    };
}

#[macro_export]
macro_rules! veprintln {
    ($($arg:tt)*) => {
        #[cfg(not(verus_only))]
        {
        use $crate::print::*;
        let s = format!($($arg)*);
        eprintln(&s)
        }
        #[cfg(verus_only)]
        {
        }
    };
}

#[verifier::external_body]
pub fn print(s: &str) {
    print!("{s}");
}

#[verifier::external_body]
pub fn eprint(s: &str) {
    eprint!("{s}");
}

#[verifier::external_body]
pub fn println(s: &str) {
    println!("{s}");
}

#[verifier::external_body]
pub fn eprintln(s: &str) {
    eprintln!("{s}");
}

#[allow(dead_code)]
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExFmtArguments<'a>(std::fmt::Arguments<'a>);

pub assume_specification[ std::fmt::format ](_0: std::fmt::Arguments<'_>) -> std::string::String
;

} // verus!
