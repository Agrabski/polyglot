import logo from './logo.svg';
import './App.css';
import wasm from '@maslox303/polyglot_js/polyglot_js';
import { evaluate } from '@maslox303/polyglot_js/polyglot_js';
function App() {

  evaluate('(= 1 1)', {
    abc: 123
  });
  return (
    <div className="App">
      <header className="App-header">
        <img src={logo} className="App-logo" alt="logo" />
        <p>
          Edit <code>src/App.js</code> and save to reload.
        </p>
        <a
          className="App-link"
          href="https://reactjs.org"
          target="_blank"
          rel="noopener noreferrer"
        >
          Learn React
        </a>
      </header>
    </div>
  );
}

export default App;
