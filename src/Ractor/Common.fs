namespace Ractor

open System
open System.Collections.Generic
open System.Threading
open System.Threading.Tasks

open Hopac
open Hopac.Extra
open Hopac.Extensions
open Hopac.Job.Infixes
open Hopac.Alt.Infixes


type Message<'T>(value:'T, hasError:bool, error:Exception) = 
    member val Value = value with get, set
    member val HasError = hasError with get, set
    member val Error = error with get, set
    new() = Message<'T>(Unchecked.defaultof<'T>, false, null)

type Envelope<'Task>(message:Message<'Task>, resultId:string, callerIds : String[]) = 
    member val Message = message with get, set
    member val ResultId = resultId  with get, set
    member val CallerIds : String[] = callerIds with get, set
    new() = Envelope<'Task>(Unchecked.defaultof<Message<'Task>>, "", [||])


type IRactorPerformanceMonitor =
    abstract AllowHighPriorityActors : unit -> bool
    abstract AllowLowPriorityActors : unit -> bool
    abstract PeriodMilliseconds : int with get



type AsyncManualResetEvent () =
    //http://blogs.msdn.com/b/pfxteam/archive/2012/02/11/10266920.aspx
    [<VolatileFieldAttribute>]
    let mutable m_tcs = TaskCompletionSource<bool>()

    member this.WaitAsync() = m_tcs.Task
    member this.Set() = m_tcs.TrySetResult(true)
    member this.Reset() =
            let rec loop () =
                let tcs = m_tcs
                if not tcs.Task.IsCompleted || 
                    Interlocked.CompareExchange(&m_tcs, new TaskCompletionSource<bool>(), tcs) = tcs then
                    ()
                else
                    loop()
            loop ()

/// <summary>
/// Hopac's alternative to http://blogs.msdn.com/b/pfxteam/archive/2012/02/11/10266920.aspx
/// </summary>
type HopacManualResetEvent (initialState : bool) =
    [<VolatileFieldAttribute>]
    let mutable state : bool = initialState
    let setChannel : MChan<bool> = run <| Multicast.create ()
    let lock = Lock.Now.create()
    new() = HopacManualResetEvent(false)

    member this.Wait() : Job<bool> =
        let rec loop () = 
            job {
                if state then return true 
                else 
                    let! port = Multicast.port setChannel
                    let! res = (Multicast.recv port) // waiting here
                    if res then return true
                    else return! loop ()
            }
        loop ()

    // From Multicast.fsi: **Sends** a message to all of the ports listening to the multicast channel.
    // Send must mean the same as in Ch
    member this.Set() : Job<unit> = 
        (Multicast.multicast setChannel true)   // there could be no waiters
        |>> (fun _ -> state <- true )   // in any case we set the state
        >>% ()                          // and return unit
        |> (Lock.duringJob lock)

    member this.Reset() : Job<unit> = 
        (Multicast.multicast setChannel false) // (redundant?) if there are takers, res in loop() will be false and loop will iterate
        |>> (fun _ -> state <- false )  // in any case we set the state
        >>% ()
        |> (Lock.duringJob lock)

type AsyncAutoResetEvent () =
    //http://blogs.msdn.com/b/pfxteam/archive/2012/02/11/10266923.aspx
    static let mutable s_completed = Task.FromResult(true)
    let m_waits = new Queue<TaskCompletionSource<bool>>()
    let mutable m_signaled = false

    member this.WaitAsync(timeout:int) = 
        Monitor.Enter(m_waits)
        try
            if m_signaled then
                m_signaled <- false
                s_completed
            else
                let ct = new CancellationTokenSource(timeout)
                let tcs = new TaskCompletionSource<bool>()
                ct.Token.Register(Action(fun _ -> tcs.TrySetResult(false) |> ignore)) |> ignore
                m_waits.Enqueue(tcs)
                tcs.Task
        finally
            Monitor.Exit(m_waits)

    member this.Set() = 
        let mutable toRelease = Unchecked.defaultof<TaskCompletionSource<bool>>
        Monitor.Enter(m_waits)
        try
            if m_waits.Count > 0 then
                toRelease <- m_waits.Dequeue() 
            else 
                if not m_signaled then m_signaled <- true
            if toRelease <> null then toRelease.TrySetResult(true) |> ignore
        finally
            Monitor.Exit(m_waits)

/// <summary>
/// MSDN: The AutoResetEvent class represents a local wait handle event that resets automatically 
/// when signaled, after releasing a single waiting thread. An AutoResetEvent object is automatically 
/// reset to non-signaled by the system after a single waiting thread has been released. 
/// If no threads are waiting, the event object's state remains signaled.
///
/// Hopac's alternative to http://blogs.msdn.com/b/pfxteam/archive/2012/02/11/10266923.aspx
/// </summary>
type HopacAutoResetEvent (initialState : bool) =
    // We will wait on take, and set with send
    let setChannel : Ch<unit> = ch()
    do if initialState then start <| Ch.send setChannel ()
    new() = HopacAutoResetEvent(false)
    member this.Wait(timeout:int) : Job<bool> = 
            let timedOut : Alt<bool> = 
                ((float timeout) |> TimeSpan.FromMilliseconds |> Timer.Global.timeOut)
                >>=? fun () -> Job.result false
            let signaled = Ch.Alt.take setChannel >>=? fun () -> Job.result true
            signaled <|> timedOut

    // From docs, important for <|>:
    // The given alternatives are processed in a left-to-right order with short-cut evaluation. 
    // In other words, given an alternative of the form first <|> second, the first alternative 
    // is first instantiated and, if it is pickable, is committed to and the second alternative 
    // will not be instantiated at all.

    member this.Set() : Job<unit> = 
        // from MSDN: Also, if Set is called when there are no threads waiting and the EventWaitHandle 
        // is already signaled, the call has no effect.

        // try take and send covers all cases
        // if there was no waiters and state was signalled -> will steal the state and send it back immediately
        // if there were waiting thread or state was not signaled -> there was no signal and we steal nothing, just signal
        (Ch.Try.take setChannel) >>. Ch.send setChannel ()




[<AutoOpenAttribute>]
module Helpers =
    
    let isSubclassOfRawGeneric(generic: Type, toCheck: Type) : bool =
        let mutable toCheck = toCheck
        let mutable res = false
        while (toCheck <> null && toCheck <> typedefof<obj>) do
            let cur = if toCheck.IsGenericType then toCheck.GetGenericTypeDefinition() else toCheck
            if generic = cur then
                res <- true
            toCheck <- toCheck.BaseType
        res

    [<ObsoleteAttribute>]
    let inline deleteRepeatingItemsInHSET (redis:Redis, hkey:string) =
        // self-containig script from params
        // set current items
        // if previous items exist, take intersect
        let lua = 
            @"  local previousKey = KEYS[1]..':previousKeys'
                local currentKey = KEYS[1]..':currentKeys'
                local currentItems = redis.call('HKEYS', KEYS[1])
                local res = 0
                redis.call('DEL', currentKey)
                if redis.call('HLEN', KEYS[1]) > 0 then
                   redis.call('SADD', currentKey, unpack(currentItems))
                   local intersect
                   if redis.call('SCARD', previousKey) > 0 then
                       intersect = redis.call('SINTER', previousKey, currentKey)
                       if #intersect > 0 then
                            redis.call('HDEL', KEYS[1], unpack(intersect))
                            res = #intersect
                       end
                   end
                end
                redis.call('DEL', previousKey)
                if #currentItems > 0 then
                    redis.call('SADD', previousKey, unpack(currentItems))
                end
                return res
            "
        Console.WriteLine("Before eval")
        redis.EvalAsync<int>(lua, [|hkey|]).Result


[<AutoOpenAttribute>]
module unnestModule = 
    let unnest3 (tuple : (('T1 * 'T2) * 'T3)  ) =
        let ((v1, v2), v3) = tuple
        v1, v2, v3

    let unnest4 (tuple : ((('T1 * 'T2) * 'T3) * 'T4)  ) =
        let (((v1, v2), v3), v4) = tuple
        v1, v2, v3, v4

    let unnest5 (tuple : (((('T1 * 'T2) * 'T3) * 'T4) * 'T5)  ) =
        let ((((v1, v2), v3), v4), v5) = tuple
        v1, v2, v3, v4, v5

    let unnest6 (tuple : ((((('T1 * 'T2) * 'T3) * 'T4) * 'T5) * 'T6)  ) =
        let (((((v1, v2), v3), v4), v5), v6) = tuple
        v1, v2, v3, v4, v5, v6

    let unnest7 (tuple : (((((('T1 * 'T2) * 'T3) * 'T4) * 'T5) * 'T6) * 'T7)  ) =
        let ((((((v1, v2), v3), v4), v5), v6), v7) = tuple
        v1, v2, v3, v4, v5, v6, v7

open System
open System.Runtime.InteropServices
open System.Runtime.CompilerServices

[<Extension>]
type TuplesExtension() =
    [<Extension>]
    static member Unnest(this : (('T1 * 'T2) * 'T3)) = 
        unnest3 this

    [<Extension>]
    static member Unnest(this : (('T1 * 'T2) * 'T3) * 'T4 ) = 
        unnest4 this

    [<Extension>]
    static member Unnest(this : (((('T1 * 'T2) * 'T3) * 'T4) * 'T5) ) = 
        unnest5 this

    [<Extension>]
    static member Unnest(this : ((((('T1 * 'T2) * 'T3) * 'T4) * 'T5) * 'T6) ) = 
        unnest6 this

    [<Extension>]
    static member Unnest(this : (((((('T1 * 'T2) * 'T3) * 'T4) * 'T5) * 'T6) * 'T7) ) = 
        unnest7 this