// Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Manages system resources that can be allocated to VMs and their devices.

#![deny(missing_docs)]

mod id_allocator;

pub use crate::id_allocator::IdAllocator;
use std::fmt;
use std::result;

/// Error type for IdAllocator usage.
#[derive(Debug, PartialEq)]
pub enum Error {
    /// All ids from the range specified are exhausted.
    Overflow,
    /// An id that is not part of the specified range was requested to be released.
    OutOfRange(u32),
    /// An id that was already released was requested to be released.
    AlreadyReleased(u32),
    /// An id  that was never allocated was requested to be released.
    NeverAllocated(u32),
    /// There are no more IDs available in the manage range
    ResourceExhausted,
    /// The range to manage is invalid.
    InvalidRange(u32, u32),
}

impl std::error::Error for Error {}

/// Wrapper over std::result::Result
pub type Result = result::Result<u32, Error>;

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Error::*;

        match *self {
            Overflow => write!(f, "Id counter overflowed."),
            OutOfRange(id) => write!(f, "Specified id: {} is not in the range.", id),
            ResourceExhausted => {
                write!(f, "There are no more available ids in the specified range.")
            }
            AlreadyReleased(id) => write!(f, "Specified id: {} is already released.", id),
            NeverAllocated(id) => write!(
                f,
                "Specified id: {} was never allocated, can't release it",
                id
            ),
            InvalidRange(begin, end) => {
                write!(f, "The range specified: {}-{} is not valid.", begin, end)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::Error as AllocError;

    #[test]
    fn test_error_messages() {
        let err = AllocError::Overflow;
        assert_eq!(format!("{}", err), "Id counter overflowed.");
        let err = AllocError::OutOfRange(3);
        assert_eq!(format!("{}", err), "Specified id: 3 is not in the range.");
        let err = AllocError::AlreadyReleased(3);
        assert_eq!(format!("{}", err), "Specified id: 3 is already released.");
        let err = AllocError::NeverAllocated(3);
        assert_eq!(
            format!("{}", err),
            "Specified id: 3 was never allocated, can't release it"
        );
        let err = AllocError::ResourceExhausted;
        assert_eq!(
            format!("{}", err),
            "There are no more available ids in the specified range."
        );
        let err = AllocError::InvalidRange(23, 5);
        assert_eq!(
            format!("{}", err),
            "The range specified: 23-5 is not valid."
        );
    }
}
