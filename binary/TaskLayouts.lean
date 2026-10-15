namespace Binary.TaskLayouts
-- Generated from the pinned fs/file{,_table}.c DWARF CUs.
def taskSize : Nat := 6400
def task_flags : Nat := 44
def task_atomic_flags : Nat := 720
def task_blocked : Nat := 1312
def task_pending_signal : Nat := 1352
def task_thread_info_flags : Nat := 0
def task_cred : Nat := 1232
def task_signal : Nat := 1296
def task_seccomp_mode : Nat := 1392
def task_seccomp_filter_count : Nat := 1396
def task_seccomp_filter : Nat := 1400
def task_task_works : Nat := 1384
def task_in_eventfd : Nat := 712
def task_in_eventfd_bit : Nat := 6
def credSize : Nat := 136
def cred_cap_effective : Nat := 64
def signalSize : Nat := 920
def signal_rlim : Nat := 592
def rlimitSize : Nat := 16
def rlimit_rlim_cur : Nat := 0
def fileSize : Nat := 168
def file_f_task_work : Nat := 136
def callbackSize : Nat := 16
def callback_next : Nat := 0
def callback_func : Nat := 8
def fputCallbackAddress : BitVec 64 := .ofNat 64 18446744071580588992
def workExitedAddress : BitVec 64 := .ofNat 64 18446744071595208112
end Binary.TaskLayouts
