/**
 * 
 */
package xhail.core;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.lang.ProcessBuilder.Redirect;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.AbstractMap.SimpleEntry;
import java.util.Collection;
import java.util.Collections;
import java.util.Map;
import java.util.ArrayList;
import java.util.concurrent.TimeUnit;

import xhail.core.entities.Grounding;
import xhail.core.entities.Problem;
import xhail.core.entities.Solvable;
import xhail.core.entities.Values;
import xhail.core.parser.Acquirer;

/**
 * @author stefano
 *
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
				this.source.toFile().deleteOnExit();
				this.middle = Files.createTempFile("xhail", ".tmp");
				this.middle.toFile().deleteOnExit();
				this.target = Files.createTempFile("xhail", ".tmp");
				this.target.toFile().deleteOnExit();
				this.errors = Files.createTempFile("xhail", ".tmp");
				this.errors.toFile().deleteOnExit();
			} catch (Exception e) {
				Logger.error("cannot send data to processes");
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

	private final String[] clasp;

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

	private Dialler(Builder builder) {
		if (null == builder)
			throw new IllegalArgumentException("Illegal 'builder' argument in Dialler(Byprocess.Builder): " + builder);

		ArrayList<String> claspCmd = new ArrayList<String>();
		claspCmd.add(builder.config.getClasp().toAbsolutePath().toString());
		claspCmd.add(builder.middle.toAbsolutePath().toString());
		claspCmd.add("--verbose=0");
		claspCmd.add("--opt-mode=optN");
		if (null != builder.values)
			claspCmd.add("--opt-bound=" + builder.values.toString());
		this.clasp = claspCmd.toArray(new String[claspCmd.size()]);

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
				handle(Files.newInputStream(errors));
				try {
					if (debug)
						Logger.message(String.format("*** Info  (%s): calling '%s'", Logger.SIGNATURE, String.join(" ", this.clasp)));
					Process clasp = new ProcessBuilder(this.clasp).redirectOutput(Redirect.to(target.toFile())).start();
					if (this.budget == 0) {
						// wait forever
						clasp.waitFor();
					} else {
						// wait for specified time and then signal process (use suboptimal answer set)
						// see http://stackoverflow.com/questions/37043114/how-to-stop-a-command-being-executed-after-4-5-seconds-through-process-builder
						clasp.waitFor(this.budget, TimeUnit.SECONDS);
						clasp.destroy();
						clasp.waitFor();
					}
					try {
						return Acquirer.from(Files.newInputStream(target)).parse();
					} catch (IOException e) {
						if (!output)
							Logger.error("cannot read from 'clasp' process");
					}
				} catch (IOException e) {
					if (!output)
						Logger.error("cannot launch 'clasp' process");
				} catch (InterruptedException e) {
					if (!output)
						Logger.error("'clasp' process was interrupted");
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
