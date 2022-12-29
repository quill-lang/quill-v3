* How can functions choose whether to return a `FnOnce` or `Fn`?
  I am pretty sure managing stuff purely via QTT doesn't suffice, since we use usage for storage info.
  This would then better map onto Rust's `Fn` trait, representing a real resource that's usable multiple times.
  Also works better with cleanup afterwards.
