/*
 * TinyEXR - isolated in-memory filesystem for the WASM source regression suite.
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors
 * SPDX-License-Identifier: BSD-3-Clause
 */
Module.preRun = Module.preRun || [];
Module.preRun.push(function () { FS.mkdir('/build'); });
