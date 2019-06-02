// Copyright (C) 2019 Alibaba Cloud Computing. All rights reserved.
// SPDX-License-Identifier: Apache-2.0
//
// Portions Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// Portions Copyright 2017 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the THIRD-PARTY file.

//! A default Unix implementation of the GuestMemory trait by mmap()-ing guest's memory into
//! the current process.
//!
//! The main structs to access guest's memory are:
//! - [MmapRegion](struct.MmapRegion.html): mmap a continuous region of guest's memory into the
//! current process
//! - [GuestRegionMmap](struct.GuestRegionMmap.html): tracks a mapping of memory in the current
//! process and the corresponding base address. It relays guest memory access requests to the
//! underline [MmapRegion](struct.MmapRegion.html) object.
//! - [GuestMemoryMmap](struct.GuestMemoryMmap.html): provides methods to access a collection of
//! GuestRegionMmap objects.

use std::fs::File;
use std::io;
use std::ptr::null_mut;

use libc;

use guest_memory::FileMappingConfig;
use mmap::AsSlice;
use volatile_memory::{self, compute_offset, VolatileMemory, VolatileSlice};

use std::os::unix::io::AsRawFd;

// TODO: when mapping an file, should we also check that offset + length is smaller than the file
// size? AFAIK, accesses past the end of the object can generate SIGBUS signals, but then again,
// even if we do verify, someone might truncate the file later. I guess it might still be a
// valuable sanity check.
// TODO: should we explicitly check that the offset is a multiple of PAGE_SIZE, or will mmap return
// an error anyway in this case?
fn mmap(file_mapping_config: Option<&FileMappingConfig>, length: usize) -> io::Result<*mut u8> {
    let (fd, flags, offset) = if let Some(config) = file_mapping_config {
        (
            config.file().as_raw_fd(),
            libc::MAP_NORESERVE | libc::MAP_SHARED,
            config.offset(),
        )
    } else {
        (
            -1,
            libc::MAP_ANONYMOUS | libc::MAP_PRIVATE | libc::MAP_NORESERVE,
            0,
        )
    };

    // Safe because all parameters are valid (or lead to immediate mmap errors).
    let addr = unsafe {
        libc::mmap(
            null_mut(),
            length,
            libc::PROT_READ | libc::PROT_WRITE,
            flags,
            fd,
            offset as libc::off_t,
        )
    };

    if addr == libc::MAP_FAILED {
        return Err(io::Error::last_os_error());
    }

    Ok(addr as *mut u8)
}

/// A backend driver to access guest's physical memory by mmapping guest's memory into the current
/// process.
/// For a combination of 32-bit hypervisor and 64-bit virtual machine, only partial of guest's
/// physical memory may be mapped into current process due to limited process virtual address
/// space size.
#[derive(Debug)]
pub struct MmapRegion {
    addr: *mut u8,
    size: usize,
    file_mapping_config: Option<FileMappingConfig>,
}

// Send and Sync aren't automatically inherited for the raw address pointer.
// Accessing that pointer is only done through the stateless interface which
// allows the object to be shared by multiple threads without a decrease in
// safety.
unsafe impl Send for MmapRegion {}
unsafe impl Sync for MmapRegion {}

impl MmapRegion {
    /// Creates an anonymous shared mapping of `size` bytes.
    ///
    /// # Arguments
    /// * `size` - Size of memory region in bytes.
    pub fn new(size: usize) -> io::Result<Self> {
        Ok(Self {
            addr: mmap(None, size)?,
            size,
            file_mapping_config: None,
        })
    }

    /// Maps the `size` bytes starting at `offset` bytes of the given `fd`.
    ///
    /// # Arguments
    /// * `fd` - File descriptor to mmap from.
    /// * `size` - Size of memory region in bytes.
    /// * `offset` - Offset in bytes from the beginning of `fd` to start the mmap.
    pub fn from_file(file: File, size: usize, offset: usize) -> io::Result<Self> {
        let file_mapping_config = Some(FileMappingConfig::new(file, offset));
        let addr = mmap(file_mapping_config.as_ref(), size)?;
        Ok(Self {
            addr,
            size,
            file_mapping_config,
        })
    }

    /// Returns a pointer to the beginning of the memory region.  Should only be
    /// used for passing this region to ioctls for setting guest memory.
    pub fn as_ptr(&self) -> *mut u8 {
        self.addr
    }

    /// Returns the configuration of the file mapping which backs this region, or `None` if
    /// we're only using anonymous memory.
    pub fn file_mapping_config(&self) -> Option<&FileMappingConfig> {
        self.file_mapping_config.as_ref()
    }
}

impl AsSlice for MmapRegion {
    // Returns the region as a slice
    // used to do crap
    unsafe fn as_slice(&self) -> &[u8] {
        // This is safe because we mapped the area at addr ourselves, so this slice will not
        // overflow. However, it is possible to alias.
        std::slice::from_raw_parts(self.addr, self.size)
    }

    // safe because it's expected interior mutability
    #[allow(clippy::mut_from_ref)]
    unsafe fn as_mut_slice(&self) -> &mut [u8] {
        // This is safe because we mapped the area at addr ourselves, so this slice will not
        // overflow. However, it is possible to alias.
        std::slice::from_raw_parts_mut(self.addr, self.size)
    }
}

impl VolatileMemory for MmapRegion {
    fn len(&self) -> usize {
        self.size
    }

    fn get_slice(&self, offset: usize, count: usize) -> volatile_memory::Result<VolatileSlice> {
        let end = compute_offset(offset, count)?;
        if end > self.size {
            return Err(volatile_memory::Error::OutOfBounds { addr: end });
        }

        // Safe because we checked that offset + count was within our range and we only ever hand
        // out volatile accessors.
        Ok(unsafe { VolatileSlice::new((self.addr as usize + offset) as *mut _, count) })
    }
}

impl Drop for MmapRegion {
    fn drop(&mut self) {
        // This is safe because we mmap the area at addr ourselves, and nobody
        // else is holding a reference to it.
        unsafe {
            libc::munmap(self.addr as *mut libc::c_void, self.size);
        }
    }
}

#[cfg(test)]
mod tests {}
