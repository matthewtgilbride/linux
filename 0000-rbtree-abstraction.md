Red-black tree abstraction needed by Rust Binder

This patchset contains the red-black tree abstractions needed by the Rust implementation of the Binder driver.

Please see the Rust Binder RFC for usage examples:
https://lore.kernel.org/rust-for-linux/20231101-rust-binder-v1-0-08ba9197f637@google.com/

Users of "rust: rbtree: add red-black tree implementation backed by the C version"
    [PATCH RFC 03/20] rust_binder: add threading support
    [PATCH RFC 05/20] rust_binder: add nodes and context managers
    [PATCH RFC 06/20] rust_binder: add oneway transactions

Users of "rust: rbtree: add `RBTreeIterator`"
    TODO: none...but it would be weird to have IteratorMut without Iterator

Users of "rust: rbtree: add `RBTreeIteratorMut`"
    [PATCH RFC 06/20] rust_binder: add oneway transactions

Users of "rust: rbtree: add `RBTreeCursor`"
    [PATCH RFC 06/20] rust_binder: add oneway transactions

To: Miguel Ojeda <ojeda@kernel.org>
To: Alex Gaynor <alex.gaynor@gmail.com>
To: Wedson Almeida Filho <wedsonaf@gmail.com>
To: Boqun Feng <boqun.feng@gmail.com>
To: Gary Guo <gary@garyguo.net>
To: Björn Roy Baron <bjorn3_gh@protonmail.com>
To: Benno Lossin <benno.lossin@proton.me>
To: Andreas Hindborg <a.hindborg@samsung.com>
To: Greg Kroah-Hartman <gregkh@linuxfoundation.org>
To: Arve Hjønnevåg <arve@android.com>
To: Todd Kjos <tkjos@android.com>
To: Carlos Llamas <cmllamas@google.com>
Cc: Matthew Wilcox <willy@infradead.org>
Cc: linux-kernel@vger.kernel.org
Cc: rust-for-linux@vger.kernel.org
Signed-off-by: Alice Ryhl <aliceryhl@google.com>