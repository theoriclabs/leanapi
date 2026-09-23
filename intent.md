Be a fully functional express/fastapi equivalent for Lean.

So mirror features:
- Routing
- End point definition
- Headers
    - Authentication => JWT, Bearer, and username/password
        - If crypto library in Lean doesn't exist, mark it as a dependency, we'll do it in a different repo

- Middlewares => We can probably fundamentally rethink middlewares when the definitions are in Lean, but v0.1, we can mirror definitions from other ecosystems.

- Abstractly and tightly define the domain we are working, and the validations to be garunteed when data cross over from the API to the application

- We want domain semantics be to carried over across LeanAPI to LeanDB (/Users/harshwork/code/LeanDB)

- We want to be able to define custom theorems, example:
    - There exist no code path accesible through the APIs, which can read data meant for another user
    - Prove APIs to be Idempotent


--- ---

Alright. So, this is the next post, and so I'll dictate the post. Okay. So the title of the post is, lean API. Okay. And this is, yeah, this is, like, a fast API or express, alternative in Lean. Now, in the past few days, I released bunch of other tools, in the lean ecosystem. There was, like, lean react, lean lean d b. I actually released this lean HTTP client two days ago as well, and, this is lean API. Okay? Bunch of people ask me, okay. What's the point? What's the point of, like, rewriting something in lean? And the the actual I'll show you with some of the examples. The primary advantage of it is you can prove properties of a program across, system boundaries. Okay? And which means, so so I I'll give three examples. Here. First is, so so what lean API does is the first time, it's two interacting with two systems. One is the, HTTP back end and, the second HTTP front. Sorry. One is the API front end. Like, it API interface and second is the database. Okay? And, now because both of the properties both of the systems are written written in LEAP or the interface are written in LEAP, that means we can, like, prove properties about the system as a whole. So first example is, like so in lean API, you can do authentication. Okay. So it handles us, and it handles, like yeah, yeah, all kind of JWT and bunch of other arts. Okay. And now, like, for example, you have a table. So, like, let's just take this example. So we have the chess table. Okay? And, there are tables on the games of a specific user. And we want to make sure only games only for the user who has their own game. The only they can see their their games, and no one else can see their see that game. Okay? Now there are, like, lot of mistakes which can happen. So first is like, okay. This this data can be exposed to some other user. We can also, like it might happen that okay. You can accidentally, so non authenticated users cannot see it. But, users from one user, if they get the game ID, they can, like, somehow get the game ID. They can watch, see the game of someone else. Okay. That can happen. And there are a lot of these things which can happen. In in lean, we can prove that there's no code path where this is happening. Okay. I'll another example will be so second example I'll talk about is we can prove that the request are item potent. And third is yes. These are two things I'll prove, okay, in our system. So, overall, what it does is, basically, it allows us to prove so we like, no amount of testing your testing can tell you that, sure. Yes. This, this bug is not there. But, as the complexity of your applications increase, it becomes harder and harder to test things. And and still bugs remain. So this what what leans lean allows us to do is to, like, bring us closer to a future where, there are no bugs.