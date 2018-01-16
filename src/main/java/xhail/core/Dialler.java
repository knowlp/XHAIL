/**
 * 
 */
package xhail.core;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.OutputStream;
import java.io.BufferedOutputStream;
import java.io.InputStream;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.PrintStream;
import java.io.InputStreamReader;
import java.lang.ProcessBuilder.Redirect;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.AbstractMap.SimpleEntry;
import java.util.Collection;
import java.util.Collections;
import java.util.Map;
import java.util.ArrayList;
import java.util.Scanner;
import java.util.concurrent.TimeUnit;

import xhail.core.entities.Grounding;
import xhail.core.entities.Problem;
import xhail.core.entities.Solvable;
import xhail.core.entities.Values;
import xhail.core.parser.Acquirer;

/**
 * @author stefano
 *
 * WASP and time budget addition by Peter Schueller <schueller.p@gmail.com>
 */
public class Dialler {

	public static class Builder implements Buildable<Dialler> {

		private Config config;
		private Path errors = null;
		private Path middle = null;
		private Solvable solvable;
		private Path source = null;
		private Path target = null;
		private Values values;

		public Builder(Config config, Grounding grounding) {
			if (null == config)
				throw new IllegalArgumentException("Illegal 'config' argument in Dialler.Builder(Config, Grounding): " + config);
			if (null == grounding)
				throw new IllegalArgumentException("Illegal 'grounding' argument in Dialler.Builder(Config, Grounding): " + grounding);
			this.config = config;
			this.solvable = grounding;
		}

		public Builder(Config config, Grounding grounding, Values values) {
			if (null == config)
				throw new IllegalArgumentException("Illegal 'config' argument in Dialler.Builder(Config, Grounding, Values): " + config);
			if (null == grounding)
				throw new IllegalArgumentException("Illegal 'grounding' argument in Dialler.Builder(Config, Grounding, Values): " + grounding);
			if (null == values)
				throw new IllegalArgumentException("Illegal 'values' argument in Dialler.Builder(Config, Grounding, Values): " + values);
			this.config = config;
			this.solvable = grounding;
			this.values = values;
		}

		public Builder(Config config, Problem problem) {
			if (null == config)
				throw new IllegalArgumentException("Illegal 'config' argument in Dialler.Builder(Config, Problem): " + config);
			if (null == problem)
				throw new IllegalArgumentException("Illegal 'problem' argument in Dialler.Builder(Config, Problem): " + problem);
			this.config = config;
			this.solvable = problem;
		}

		@Override
		public Dialler build() {
			try {
				this.source = Files.createTempFile("xhail", ".tmp");
				//this.source.toFile().deleteOnExit();
				this.middle = Files.createTempFile("xhail", ".tmp");
				//this.middle.toFile().deleteOnExit();
				this.target = Files.createTempFile("xhail", ".tmp");
				//this.target.toFile().deleteOnExit();
				this.errors = Files.createTempFile("xhail", ".tmp");
				//this.errors.toFile().deleteOnExit();
			} catch (Exception e) {
				Logger.error("cannot send data to processes:" + e.toString());
			}
			return new Dialler(this);
		}

	}

	private static int calls = 0;

	private static final String ERROR = "ERROR: ";

	private static final String WARNING = "% warning: ";

	public static final int calls() {
		return calls;
	}

	private final String[] solver;

	private final Path errors;

	private final String[] gringo;

	private final Path middle;

	private final boolean mute;

	private final Solvable solvable;

	private final Path source;

	private final Path target;

	private final boolean output;

	private final boolean debug;

	private final long budget;

	private class Stream2Stream extends Thread {
		String name;
		InputStream i;
		OutputStream o;
							    
		Stream2Stream(String name, InputStream i, OutputStream o) {
			this.name = name;
			this.i = i;
			this.o = o;
		}

		public void closeall() {
			//System.err.println("Stream2Stream("+this.name+") closing");
			// try to close both in every case
			try { i.close(); } catch (Exception e) { }
			try { o.close(); } catch (Exception e) { }
		}

		public void run() {
			int totalread = 0;
			try {
				byte[] buffer = new byte[1024];
				int read = 0;
				while((read = i.read(buffer)) != -1) {
							o.write(buffer, 0, read);
							totalread += read;
				}
				//System.err.println(String.format("Stream2Stream("+this.name+") after reading %d bytes", totalread));
			} catch (IOException e) {
				Logger.message("Stream2Stream("+this.name+") exception");
				e.printStackTrace();  
			}
			closeall();
		}
	}

	private class Stream2StreamLogging extends Stream2Stream {
		long starttime;
		String what;
		PrintStream o;

		Stream2StreamLogging(InputStream i, PrintStream o, String what) {
			super(what, i, o);
			this.starttime = System.nanoTime();
			this.what = what;
			this.o = o;
		}

		@Override
		public void run() {
			int totallines = 0;
			try {
				Scanner sc = new Scanner(this.i);
				while (sc.hasNextLine()) {
					String s = sc.nextLine();
					Logger.message(String.format("[%s %.2f s] %s", this.what, (System.nanoTime()-starttime)/(1000.0*1000.0*1000.0), s));
					this.o.println(s);
					totallines += 1;
				}
				Logger.message(String.format("[%s %.2f s] end after %d lines", this.what, (System.nanoTime()-starttime)/(1000.0*1000.0*1000.0), totallines));
			} catch (Exception e) {
				Logger.message("Stream2StreamLogging("+this.name+") exception");
				e.printStackTrace();  
			}
			closeall();
		}
	}

	private Dialler(Builder builder) {
		if (null == builder)
			throw new IllegalArgumentException("Illegal 'builder' argument in Dialler(Byprocess.Builder): " + builder);

		ArrayList<String> solverCmd = new ArrayList<String>();
		String solverString = builder.config.getClasp().toAbsolutePath().toString();
		solverCmd.add(solverString);
		if (!solverString.contains("wasp")) {
			// clasp options
			solverCmd.add("--verbose=0");
			if (null == builder.values)
				solverCmd.add("--opt-mode=optN");
			else
				solverCmd.add("--opt-mode=optN," + builder.values.toString());
		} else {
			// wasp options
			// works with git version 1c1d45 and above
			solverCmd.add("--minisat-policy");
			//solverCmd.add("--weakconstraints-algorithm=one");
			solverCmd.add("--enable-disjcores");
			solverCmd.add("--trim-core");
			solverCmd.add("--compute-firstmodel=30");
			//solverCmd.add("--weakconstraints-algorithm=interleaving-choices");
			//solverCmd.add("--weakconstraints-algorithm=interleaving-restarts");
			solverCmd.add("--printbounds");
			solverCmd.add("--shrinking-strategy=progression");
			solverCmd.add("--shrinking-budget=30"); // maybe increase this for really big instances?
			solverCmd.add("--silent=0"); // very important for parseable output
			if (null != builder.values)
				Logger.message("wasp does not support preset of cost function!");
		}
		this.solver = solverCmd.toArray(new String[solverCmd.size()]);

		this.debug = builder.config.isDebug();
		this.errors = builder.errors.toAbsolutePath();

		ArrayList<String> gringoCmd = new ArrayList<String>();
		gringoCmd.add(builder.config.getGringo().toAbsolutePath().toString());
		gringoCmd.add(builder.source.toAbsolutePath().toString());
		this.gringo = gringoCmd.toArray(new String[gringoCmd.size()]);

		this.middle = builder.middle.toAbsolutePath();
		this.mute = builder.config.isMute();
		this.output = builder.config.isOutput();
		this.solvable = builder.solvable;
		this.source = builder.source.toAbsolutePath();
		this.target = builder.target.toAbsolutePath();
		this.budget = builder.config.getBudget();
	}

	public Map.Entry<Values, Collection<Collection<String>>> execute(int iter) {
		if (iter < 0)
			throw new IllegalArgumentException("Illegal 'iter' argument in Dialler.execute(int): " + iter);
		calls += 1;
		try {
			solvable.save(iter, Files.newOutputStream(source));
			try {
				if (debug)
					Logger.message(String.format("*** Info  (%s): calling '%s'", Logger.SIGNATURE, String.join(" ", this.gringo)));
				Process gringo = new ProcessBuilder(this.gringo) //
						.redirectError(Redirect.to(errors.toFile())).redirectOutput(Redirect.to(middle.toFile())).start();
				gringo.waitFor();
				// here gringo has finished and its output is in file 'middle'
				handle(Files.newInputStream(errors));
				try {
					if (debug) {
						Logger.message(String.format("*** Info  (%s): calling '%s' with budget %d", Logger.SIGNATURE, String.join(" ", this.solver), this.budget));
					}
					Process solver = new ProcessBuilder(this.solver)
						.redirectError(Redirect.INHERIT) // show stderr with xhail stderr
						.start(); // start and return process

					InputStream fis = new FileInputStream(middle.toFile());
					// create thread that copies the contents of 'middle' to input of the solver
					Thread middle2solver = new Stream2Stream("middle2solver", fis, solver.getOutputStream());
					// copy from grounder to solver
					middle2solver.start();

					// read from standard output and write to file
					// (and print in debug mode including timestamp)
					PrintStream os = new PrintStream(new BufferedOutputStream(new FileOutputStream(target.toFile())));
					InputStream sis = solver.getInputStream();
					Thread solver2output = null;
					if (debug) {
						// line-based and logging with time
						solver2output = new Stream2StreamLogging(sis, os, "slv");
					} else {
						// just copying
						solver2output = new Stream2Stream("solver2output", sis, os);
					}
					solver2output.start();

					// wait for termination
					if (this.budget == 0) {
						// wait forever
						solver.waitFor();
					} else {
						// wait for specified time and then signal process (use suboptimal answer set)
						// see http://stackoverflow.com/questions/37043114/how-to-stop-a-command-being-executed-after-4-5-seconds-through-process-builder
						solver.waitFor(this.budget, TimeUnit.SECONDS);

						try {
							int ex = solver.exitValue(); // throws if did not terminate

							// wait a bit (250 ms) for grounder output to be sent
							// (or for thread to die from io exception)
							middle2solver.join(250);

							// same for solver output to be processed
							solver2output.join(250);
						} catch(IllegalThreadStateException e) {
							// thread did not terminate yet!
							Logger.message(String.format("solver process did not terminate, killing!"));
							// really kill
							solver.destroy();
							solver.waitFor();
						}
					}
					if( solver.exitValue() != 30 || debug ) {
						Logger.message(String.format("solver process ended with exit value %d (expect 30)!", solver.exitValue()));
					}

					// wait for grounder output to be sent (or for thread to die from io exception)
					middle2solver.join();

					// wait for solver output to be processed (or for thread to die from io exception)
					solver2output.join();

					try {
						//System.err.println("Dialler reading from target file '"+target+"'");
						return Acquirer.from(Files.newInputStream(target)).parse();
					} catch (IOException e) {
						if (!output)
							Logger.error("cannot read from solver process");
					}
				} catch (IOException e) {
					if (!output)
						Logger.error("cannot launch solver process");
				} catch (InterruptedException e) {
					if (!output)
						Logger.error("solver process was interrupted");
				}
			} catch (IOException e) {
				if (!output)
					Logger.error("cannot launch 'gringo' process");
			} catch (InterruptedException e) {
				if (!output)
					Logger.error("'gringo' process was interrupted");
			}
		} catch (IOException e) {
			if (!output)
				Logger.error("cannot write to 'gringo' process");
		}
		return new SimpleEntry<Values, Collection<Collection<String>>>(null, Collections.emptySet());
	}

	private void handle(InputStream stream) {
		if (null == stream)
			throw new IllegalArgumentException("Illegal 'stream' argument in Dialler.handle(InputStream): " + stream);
		String line, message = "";
		try {
			BufferedReader reader = new BufferedReader(new InputStreamReader(stream));
			while (null != (line = reader.readLine())) {
				line = line.trim();
				if (!line.isEmpty()) {
					if (!message.isEmpty())
						message += "\n  " + line;
					else if (line.startsWith(ERROR))
						message = line.substring(ERROR.length());
					else if (line.startsWith(WARNING)) {
						String content = line.substring(WARNING.length());
						if (!"bad_solution/0 is never defined".equals(content) && !"number_abduced/2 is never defined".equals(content))
							Logger.warning(mute, content);
					} else
						System.err.println(line);
				}
			}
			reader.close();
		} catch (IOException e) {
			Logger.error("cannot read from child process' 'stderr'");
		}
		if (!message.isEmpty())
			Logger.error(message);
	}

}

// vim:noet:
